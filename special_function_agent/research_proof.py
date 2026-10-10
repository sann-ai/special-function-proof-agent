"""Apply fixed, fully proved real research lemmas through regenerated Lean only."""
from __future__ import annotations

import json
import re

from .core import InputError, NeedsConditions, _keys, _sha, audit_axioms, environment
from . import real_bessel, real_special

FORMAL_SCOPE = 'composition of validated real research lemmas under the fixed target assumptions'
MAX_PLAN_BYTES = 262144
MAX_PACKAGES = 12
MAX_USES = 12
MAX_DEPTH = 4
_PREAMBLE = 'import SpecialFunctionProofAgent\n\nopen scoped Real\nopen MeasureTheory\n\n'
_AUDIT = ('\n#eval IO.println "BESSEL_AUDIT_BEGIN"\n'
          '#print axioms BesselAgentCandidate.target\n'
          '#eval IO.println "BESSEL_AUDIT_END"\n')
_ID = re.compile(r'[0-9a-f]{64}\Z')


def is_research(data):
    """Recognize research-shaped plans before the ordinary closed-recipe dispatch."""
    if not isinstance(data, dict) or not isinstance(data.get('proof'), dict):
        return False
    proof = data['proof']
    return ('lemmas' in proof or 'uses' in proof or proof.get('recipe') == 'research'
            or isinstance(proof.get('steps'), list) and any(
                isinstance(step, dict) and (step.get('recipe') == 'research' or 'uses' in step)
                for step in proof['steps']))


def _bounded(data):
    try:
        raw = (json.dumps(data, ensure_ascii=False, indent=2, allow_nan=False)+'\n').encode('utf-8')
    except (ValueError, TypeError, RecursionError, UnicodeError) as exc:
        raise InputError('A research plan must be bounded finite UTF-8 JSON.') from exc
    if len(raw) > MAX_PLAN_BYTES:
        raise InputError('A research plan exceeds the 256 KiB limit.')


def _target(data):
    if not isinstance(data, dict):
        raise InputError('A research target must be a structured object.')
    target = {key: value for key, value in data.items() if key != 'proof'}
    from . import research_functions
    if research_functions.contains(target):
        research_functions.validate_target(target, require_proof=False)
    else:
        real_bessel.validate(target, require_proof=False)
    if any(kind != 'real' for kind in target['variables'].values()):
        raise InputError('Research lemma application currently requires all free variables to be real.')
    return target


def _expected_scope(data):
    from . import research_functions, defined_proof
    if research_functions.contains(data):
        return defined_proof.FORMAL_SCOPE
    if is_research(data):
        return FORMAL_SCOPE
    if real_special.cross_complete.complete_target(data):
        return real_special.cross_complete.FORMAL_SCOPE
    if real_special.bessel_y_integer.complete_target(data):
        return real_special.bessel_y_integer.formal_scope(data)
    if real_special.bessel_y_formal.contains(data):
        return real_special.bessel_y_formal.FORMAL_SCOPE
    return None


def _merge(infos):
    result, seen = [], set()
    for info in infos:
        for item in [*info['dependencies'], info]:
            if item['id'] not in seen:
                result.append(item)
                seen.add(item['id'])
    return result


def _source(body, dependencies):
    declarations = [f'namespace ResearchLemma_{info["id"]}\n\n{info["body"]}\n'
                    f'end ResearchLemma_{info["id"]}' for info in dependencies]
    declarations.append(f'namespace BesselAgentCandidate\n\n{body}\nend BesselAgentCandidate')
    return _PREAMBLE + '\n\n'.join(declarations) + '\n' + _AUDIT


def _ordinary_body(source):
    prefix = _PREAMBLE + 'namespace BesselAgentCandidate\n\n'
    suffix = '\nend BesselAgentCandidate\n' + _AUDIT
    if not source.startswith(prefix) or not source.endswith(suffix):
        raise InputError('The registered renderer has an unsupported certificate layout.')
    return source[len(prefix):-len(suffix)]


def _package(package, context, depth):
    from .research_library import read_evidence_json, validate_package
    from .defined_proof import conventions
    from .archive import target_hash
    validate_package(package)
    key = package['id']
    if depth > MAX_DEPTH or key in context['active']:
        raise InputError('Research dependencies exceed the depth limit or contain a cycle.')
    if key in context['cache']:
        info = context['cache'][key]
        if depth + info['height'] - 1 > MAX_DEPTH:
            raise InputError('Research dependencies exceed the depth limit.')
        return info
    context['seen'].add(key)
    if len(context['seen']) > MAX_PACKAGES:
        raise InputError('At most twelve research packages may occur in the dependency closure.')
    context['active'].add(key)
    request = read_evidence_json(package, 'request.json')
    result = read_evidence_json(package, 'result.json')
    _target(request)
    from . import research_functions, defined_proof
    defined = research_functions.contains(request)
    expanded = research_functions.expand_target(request) if defined else request
    if (result.get('status') != 'proved' or result.get('full_function_proof') is not True
            or result.get('certificate_kind') != 'proof'):
        raise InputError('Only full proved research lemma certificates may be applied.')
    if result.get('environment') != context['environment'] or result.get('conventions') != conventions(request):
        raise InputError('The research lemma mathematical environment or conventions changed.')
    scope = _expected_scope(request)
    if result.get('formal_scope') != scope:
        raise InputError('The research lemma formal scope differs from its fixed target.')
    bessel_target = (real_special.cross_complete.complete_target(expanded)
                     or real_special.bessel_y_integer.complete_target(expanded)
                     or real_special.bessel_y_formal.contains(expanded))
    if bessel_target and result.get('full_bessel_proof') is not True:
        raise InputError('A Bessel research lemma requires a full Bessel certificate.')
    if not bessel_target and 'full_bessel_proof' in result:
        raise InputError('The research lemma Bessel flag differs from its fixed proof scope.')
    if result.get('request_sha256') != _sha(package['evidence']['request.json'].encode()):
        raise InputError('The research lemma request digest changed.')
    if result.get('statement') != real_bessel.display(request['lhs'])+' = '+real_bessel.display(request['rhs']) or result.get('conditions') != real_bessel.labels(request):
        raise InputError('The research lemma statement or conditions differ from its request.')
    attempts = result.get('attempts')
    if not isinstance(attempts, list):
        raise InputError('The research lemma accepted audit records are missing.')
    conditional = result.get('conditional_lean', {})
    if not isinstance(conditional, dict) or conditional.get('accepted'):
        raise InputError('Conditional evidence cannot supply a full research lemma.')
    accepted = [attempt for attempt in attempts
                if isinstance(attempt, dict) and attempt.get('accepted') is True]
    if not accepted:
        raise InputError('A research lemma needs an accepted standard-axiom audit record.')
    for attempt in accepted:
        if not isinstance(attempt.get('stdout'), str):
            raise InputError('The research lemma audit output is missing.')
        axioms = audit_axioms(attempt['stdout'])
        if attempt.get('axioms') != axioms:
            raise InputError('The research lemma recorded axioms differ from its audit output.')
    if is_research(request):
        body, dependencies = _prepare(request, context, depth)
        regenerated = _source(body, dependencies)
        metadata = [info['metadata'] for info in dependencies]
        analysis = {'recipe': 'research', 'dependencies': metadata}
        if defined:
            analysis = defined_proof.analysis(request, analysis)
        if (result.get('research_dependencies') != metadata
                or result.get('analysis') != analysis):
            raise InputError('The derived research lemma dependency records differ from its fixed request.')
    else:
        if defined:
            research_functions.validate_target(request)
        else:
            real_bessel.validate(expanded)
        _domains(expanded, expanded['lhs'], expanded['rhs'])
        if not defined and not real_special.has_special(request):
            raise InputError('The source lemma needs a registered complete real-function renderer.')
        regenerated = real_special.render(request)
        body, dependencies = _ordinary_body(regenerated), []
        analysis = real_special.match_identity(expanded['lhs'], expanded['rhs'])
        if defined:
            analysis = defined_proof.analysis(request, analysis)
        if result.get('analysis') != analysis:
            raise InputError('The research lemma analysis differs from its fixed request.')
    if defined and result.get('definition_dependencies') != research_functions.metadata(request['definitions']):
        raise InputError('The research lemma function definition records changed.')
    evidence = package['evidence']
    if evidence.get('certificate.lean') != regenerated or result.get('certificate_sha256') != _sha(regenerated.encode()):
        raise InputError('The research lemma certificate differs from its regenerated fixed request.')
    if 'proof_attempt.lean' in evidence and evidence['proof_attempt.lean'] != regenerated:
        raise InputError('The research lemma proof attempt differs from its fixed certificate.')
    if 'analysis.json' in evidence:
        expected = result.get('analysis') or {'status': 'no_matching_template'}
        if read_evidence_json(package, 'analysis.json') != expected:
            raise InputError('The research lemma analysis differs from its saved result.')
    info = {'id': key, 'request': request, 'body': body, 'dependencies': dependencies,
            'height': 1 + max((item['height'] for item in dependencies), default=0),
            'metadata': {'id': key, 'name': package['name'], 'source': package['source'],
                         'target_sha256': target_hash(request),
                         'statement': result['statement'], 'conditions': result['conditions'],
                         'proof_mode': request['proof']['mode'], 'formal_scope': scope}}
    if defined:
        info['metadata']['definitions'] = research_functions.metadata(request['definitions'])
    context['active'].remove(key)
    context['cache'][key] = info
    return info


def _domains(data, lhs, rhs):
    target = {**data, 'lhs': lhs, 'rhs': rhs}
    bounds = real_bessel.domains(data)
    derived = {'id': 'cross_product_root_fraction'} if real_special.cross_complete.complete_target(target) else None
    pending = real_bessel.domain_obligations(target, derived)
    pending += [real_bessel.display(node['arg'])+' > 0'
                for node in real_bessel._walk([lhs, rhs])
                if node.get('op') == 'gamma' and not real_bessel._positive(node['arg'], bounds)]
    if pending:
        raise NeedsConditions('Research expression domain conditions are required: '+', '.join(sorted(set(pending))))


def _uses(uses, packages, data):
    variables, bounds = data['variables'], real_bessel.domains(data)
    if not isinstance(uses, list) or not 1 <= len(uses) <= MAX_USES:
        raise InputError('A research application needs one to twelve explicit lemma uses.')
    for use in uses:
        _keys(use, {'lemma', 'arguments', 'reverse'})
        if not isinstance(use['lemma'], str) or not _ID.fullmatch(use['lemma']) or use['lemma'] not in packages:
            raise InputError('Every research use must reference an included package ID.')
        if type(use['reverse']) is not bool or not isinstance(use['arguments'], dict):
            raise InputError('A research use requires an argument object and a boolean reverse flag.')
        request = packages[use['lemma']]['request']
        if set(use['arguments']) != set(request['variables']):
            raise InputError('Research arguments must cover exactly the source lemma variables.')
        for argument in use['arguments'].values():
            real_bessel._validate_expr(argument, variables)
            if any(node.get('op') in {'deriv', 'integral'} for node in real_bessel._walk(argument)):
                raise InputError('Research substitution arguments currently exclude derivatives and integrals.')
            real_bessel.validate_order_domains(argument, bounds)
            _domains(data, argument, {'op': 'int', 'value': 0})


def _apply(uses, packages, names, types):
    lines, facts = [], []
    for i, use in enumerate(uses, 1):
        source = packages[use['lemma']]['request']
        args = [f'({real_special.lean_expr(use["arguments"][name], names, types)})'
                for name in sorted(source['variables'])]
        args += ['(by nlinarith)'] * len(source['assumptions'])
        from .research_functions import contains
        theorem = 'expanded_target' if contains(source) else 'target'
        fact = f'(ResearchLemma_{use["lemma"]}.{theorem} {" ".join(args)})'
        if use['reverse']:
            fact += '.symm'
        local = f'research_use_{i}'
        lines.append(f'have {local} := {fact}')
        facts.append(local)
    lines += ['ring_nf at '+' '.join(facts)+' ⊢ <;> (simp only ['+', '.join(facts)+'] <;> ring)']
    return lines


def _prepare(data, context, depth):
    _bounded(data)
    _target(data)
    from . import research_functions, defined_proof
    if research_functions.contains(data):
        research_functions.validate_target(data)
        body, dependencies = _prepare(research_functions.expand_target(data), context, depth)
        return defined_proof.wrap_body(data, body), dependencies
    proof = data.get('proof')
    if not isinstance(proof, dict):
        raise InputError('A research proof must be an object.')
    mode = proof.get('mode')
    if mode == 'direct':
        _keys(proof, {'mode', 'recipe', 'uses', 'lemmas'})
        if proof['recipe'] != 'research':
            raise InputError('A direct research proof requires recipe research.')
    elif mode == 'steps':
        _keys(proof, {'mode', 'steps', 'lemmas'})
        if not isinstance(proof['steps'], list) or not 1 <= len(proof['steps']) <= 12:
            raise InputError('A research step proof needs one to twelve equality steps.')
    else:
        raise InputError('Research proof mode must be direct or steps.')
    snapshots = proof['lemmas']
    if not isinstance(snapshots, list) or not 1 <= len(snapshots) <= MAX_PACKAGES:
        raise InputError('A research proof needs one to twelve package snapshots.')
    packages = {}
    for snapshot in snapshots:
        info = _package(snapshot, context, depth+1)
        if info['id'] in packages:
            raise InputError('Research package IDs must be distinct.')
        packages[info['id']] = info
    _domains(data, data['lhs'], data['rhs'])
    if mode == 'direct':
        _uses(proof['uses'], packages, data)
    else:
        previous, total = data['lhs'], 0
        for step in proof['steps']:
            _keys(step, {'before', 'after', 'recipe', 'uses', 'reason', 'conditions'})
            for side in ('before', 'after'):
                real_bessel._validate_expr(step[side], data['variables'])
                real_bessel.validate_order_domains(step[side], real_bessel.domains(data))
            _domains(data, step['before'], step['after'])
            if step['before'] != previous:
                raise InputError('Research steps must preserve consecutive fixed equality endpoints.')
            if not isinstance(step['reason'], str) or len(step['reason']) > 2000:
                raise InputError('Research step reasons must be text of at most 2000 characters.')
            if not isinstance(step['conditions'], list) or any(not isinstance(c, str) or c not in real_bessel.labels(data) for c in step['conditions']):
                raise InputError('Research step conditions must come from the fixed target.')
            if step['recipe'] == 'research':
                _uses(step['uses'], packages, data)
                total += len(step['uses'])
            elif step['recipe'] != 'ring' or step['uses'] != []:
                raise InputError('Use research applications or a ring step with no lemma uses.')
            previous = step['after']
        if previous != data['rhs'] or not 1 <= total <= MAX_USES:
            raise InputError('Research steps must reach the original right side using at most twelve lemma applications.')
    names = {name: f'v{i}' for i, name in enumerate(sorted(data['variables']))}
    types = data['variables']
    expr = lambda node: real_special.lean_expr(node, names, types)
    binders = ' '.join(f'({names[name]} : ℝ)' for name in sorted(names))
    conditions = ' '.join(f'(h{i} : {real_special._condition(atom, names, types)})'
                          for i, atom in enumerate(data['assumptions']))
    lines = [f'theorem target {binders} {conditions} : {expr(data["lhs"])} = {expr(data["rhs"])} := by']
    if mode == 'direct':
        lines += ['  '+line for line in _apply(proof['uses'], packages, names, types)]
    else:
        for i, step in enumerate(proof['steps'], 1):
            lines.append(f'  have step_{i} : {expr(step["before"])} = {expr(step["after"])} := by')
            tactics = ['ring_nf <;> ring'] if step['recipe'] == 'ring' else _apply(step['uses'], packages, names, types)
            lines += ['    '+line for line in tactics]
        chain = 'step_1'
        for i in range(2, len(proof['steps'])+1):
            chain = f'({chain}).trans step_{i}'
        lines.append(f'  exact {chain}')
    return '\n'.join(lines)+'\n', _merge(packages.values())


def _validated(data):
    context = {'cache': {}, 'active': set(), 'seen': set(), 'environment': environment()}
    return _prepare(data, context, 0)


def validate_proof(data):
    """Check the closed plan and evidence; Lean discharges all source assumptions."""
    _validated(data)


def render(data):
    """Render a fixed target and regenerated, namespaced dependency theorems."""
    body, dependencies = _validated(data)
    return _source(body, dependencies)


def inspect_dependencies(data):
    """Return deterministic metadata for every transitive applied package."""
    _, dependencies = _validated(data)
    return [info['metadata'] for info in dependencies]


def inspect_packages(packages):
    """Inspect selected snapshots before generation, without executing saved Lean."""
    _bounded(packages)
    if not isinstance(packages, list) or not 1 <= len(packages) <= MAX_PACKAGES:
        raise InputError('Select one to twelve research package snapshots.')
    context = {'cache': {}, 'active': set(), 'seen': set(), 'environment': environment()}
    infos = [_package(package, context, 1) for package in packages]
    if len({info['id'] for info in infos}) != len(infos):
        raise InputError('Research package IDs must be distinct.')
    return [info['metadata'] for info in _merge(infos)]
