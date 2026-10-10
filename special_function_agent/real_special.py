"""Closed real Gamma/Beta proof recipes, preserving the entire fixed target."""
from __future__ import annotations

from copy import deepcopy
from fractions import Fraction

from .core import InputError, NeedsConditions, _keys, _run_lean, _save_json, _sha, environment
from .registry import conventions
from . import classical, orthogonal, bessel_y_formal, bessel_y_integer, cross_complete

RECIPES = ('gamma_recurrence', 'beta_integral', 'gamma_scaled_integral', 'ring') + classical.RECIPES + orthogonal.RECIPES + bessel_y_formal.RECIPES + bessel_y_integer.RECIPES + cross_complete.RECIPES
SPECIAL_OPS = {'gamma', 'exp', 'rpow', 'integral', 'hermite_h', 'hermite_he', 'legendre', 'laguerre', 'jacobi', 'bessel_y_noninteger', 'erf', 'pi', 'sqrt', 'deriv'}


def has_special(data):
    from .real_bessel import _walk
    nodes = list(_walk([data.get('lhs'), data.get('rhs'), data.get('assumptions', [])]))
    proof = data.get('proof')
    if (data.get('schema_version') == 2 and (bessel_y_integer.complete_target(data) or cross_complete.complete_target(data))
            and not (isinstance(proof, dict) and proof.get('mode') == 'diagnostic')):
        return True
    return (data.get('schema_version') == 2 and any(n.get('op') in SPECIAL_OPS for n in nodes)
            and not any(n.get('op') in {'bessel_y', 'bessel_cross'} for n in nodes))


def validate_proof(data):
    from .real_bessel import _validate_expr, labels, validate_order_domains, domains
    if 'proof' not in data:
        return
    proof = data['proof']
    if not isinstance(proof, dict):
        raise InputError('A proof plan must be an object.')
    mode = proof.get('mode')
    if mode == 'diagnostic':
        _keys(proof, {'mode'})
    elif mode == 'direct':
        _keys(proof, {'mode', 'recipe'})
        if proof['recipe'] not in RECIPES:
            raise InputError('Unknown real special-function recipe.')
    elif mode == 'steps':
        _keys(proof, {'mode', 'steps'})
        steps = proof['steps']
        if not isinstance(steps, list) or not 1 <= len(steps) <= 12:
            raise InputError('A step proof needs one to twelve equality steps.')
        previous = data['lhs']
        for step in steps:
            _keys(step, {'before', 'after', 'recipe', 'reason', 'conditions'})
            for side in ('before', 'after'):
                _validate_expr(step[side], data['variables'])
                validate_order_domains(step[side], domains(data))
            if step['before'] != previous:
                raise InputError('Every step must start at the preceding fixed endpoint.')
            if step['recipe'] not in RECIPES or not isinstance(step['reason'], str) or len(step['reason']) > 2000:
                raise InputError('Use a registered recipe and a short reason.')
            if not isinstance(step['conditions'], list) or any(not isinstance(c, str) or c not in labels(data) for c in step['conditions']):
                raise InputError('Step conditions must be drawn from the exact target conditions.')
            previous = step['after']
        if previous != data['rhs']:
            raise InputError('The last step must end at the original right-hand side.')
    else:
        raise InputError('Use direct, steps, or diagnostic proof mode.')


def _var(name): return {'op': 'var', 'name': name}
def _int(value): return {'op': 'int', 'value': value}
def _bin(op, a, b): return {'op': op, 'args': [a, b]}
def _gamma(arg): return {'op': 'gamma', 'arg': arg}
def _neg(arg): return {'op': 'neg', 'arg': arg}
def _rpow(a, b): return {'op': 'rpow', 'base': a, 'exponent': b}


def match_identity(lhs, rhs):
    """Match only the three proved formulas, independent of free/bound names."""
    for left, right, reverse in ((lhs, rhs, False), (rhs, lhs, True)):
        if left.get('op') == 'gamma':
            arg = left['arg']
            if arg.get('op') == 'add' and arg['args'][1] == _int(1):
                x = arg['args'][0]
                if x.get('op') == 'var' and right == _bin('mul', x, _gamma(x)):
                    return {'recipe': 'gamma_recurrence', 'arguments': [x], 'reverse': reverse}
        if left.get('op') == 'integral' and left['lower'] == _int(0):
            t = _var(left['var'])
            body = left['body']
            if body.get('op') != 'mul': continue
            first, second = body['args']
            if first.get('op') != 'rpow' or first['base'] != t: continue
            exponent = first['exponent']
            if exponent.get('op') != 'sub' or exponent['args'][1] != _int(1): continue
            a = exponent['args'][0]
            if a.get('op') != 'var': continue
            if left['upper'] == _int(1) and second.get('op') == 'rpow' and second['base'] == _bin('sub', _int(1), t):
                exponent = second['exponent']
                if exponent.get('op') != 'sub' or exponent['args'][1] != _int(1): continue
                b = exponent['args'][0]
                if b.get('op') == 'var' and right == _bin('div', _bin('mul', _gamma(a), _gamma(b)), _gamma(_bin('add', a, b))):
                    return {'recipe': 'beta_integral', 'arguments': [a, b], 'reverse': reverse}
            if left['upper'] == {'op': 'infinity'} and second.get('op') == 'exp':
                arg = second['arg']
                if arg.get('op') == 'mul' and arg['args'][0].get('op') == 'neg' and arg['args'][1] == t:
                    r = arg['args'][0]['arg']
                elif arg.get('op') == 'neg' and arg['arg'].get('op') == 'mul' and arg['arg']['args'][1] == t:
                    r = arg['arg']['args'][0]
                else: continue
                if r.get('op') == 'var' and right == _bin('mul', _rpow(r, _neg(a)), _gamma(a)):
                    return {'recipe': 'gamma_scaled_integral', 'arguments': [a, r], 'reverse': reverse}
    return classical.match(lhs, rhs) or orthogonal.match(lhs, rhs) or bessel_y_formal.match(lhs, rhs) or bessel_y_integer.match_identity(lhs, rhs) or cross_complete.match_identity(lhs, rhs)


def default_proof(data, route='direct'):
    from .real_bessel import labels
    matched = match_identity(data['lhs'], data['rhs'])
    recipe = matched['recipe'] if matched else 'ring'
    if route == 'diagnostic': return {'mode': route}
    if route == 'direct': return {'mode': route, 'recipe': recipe}
    reasons = {'gamma_recurrence': '正の引数におけるGammaの漸化式を適用する。',
               'beta_integral': '正の2パラメータに対するEulerのBeta積分を適用する。',
               'gamma_scaled_integral': '正の形状・尺度パラメータに対するGamma積分を適用する。',
               'ring': '元の全条件の下で実数の代数式を整理する。'}
    reasons.update(classical.REASONS)
    reasons.update(orthogonal.REASONS)
    reasons.update(bessel_y_formal.REASONS)
    reasons.update(bessel_y_integer.REASONS)
    reasons.update(cross_complete.REASONS)
    return {'mode': 'steps', 'steps': [{'before': deepcopy(data['lhs']), 'after': deepcopy(data['rhs']),
             'recipe': recipe, 'reason': reasons[recipe], 'conditions': labels(data)}]}


def lean_expr(node, names, types=None):
    types = types or {}
    op = node['op']
    ev = lambda n: lean_expr(n, names, types)
    if op == 'int': return f'({node["value"]} : ℝ)'
    if op == 'var':
        value = names[node['name']]
        return f'({value} : ℝ)' if types.get(node['name']) in {'nat', 'int'} else value
    if op == 'rational': return f'({node["numerator"]} / {node["denominator"]} : ℝ)'
    if op == 'pi': return 'Real.pi'
    if op == 'sqrt': return f'(Real.sqrt {ev(node["arg"])})'
    if op == 'erf': return f'(SpecialFunctionProofAgent.erf {ev(node["arg"])})'
    if op in {'hermite_h', 'hermite_he'}:
        fn = 'hermiteH' if op == 'hermite_h' else 'hermiteHe'
        return f'(SpecialFunctionProofAgent.{fn} {classical.lean_natural(node["order"], names)} {ev(node["arg"])})'
    if op in {'legendre', 'laguerre', 'jacobi'}:
        fn = {'legendre': 'legendreP', 'laguerre': 'laguerreL', 'jacobi': 'jacobiP'}[op]
        parameters = ([node['alpha']] if op in {'laguerre', 'jacobi'} else []) + ([node['beta']] if op == 'jacobi' else [])
        args = ' '.join([classical.lean_natural(node['order'], names), *map(ev, parameters), ev(node['arg'])])
        return f'(SpecialFunctionProofAgent.{fn} {args})'
    if op == 'bessel_y_noninteger':
        return f'(SpecialFunctionProofAgent.besselYNoninteger {ev(node["order"])} {ev(node["arg"])})'
    if op == 'bessel_y':
        return f'(SpecialFunctionProofAgent.besselYInt {bessel_y_integer.lean_integer(node["order"], names)} {ev(node["arg"])})'
    if op == 'bessel_j':
        return f'(SpecialFunctionProofAgent.realBesselJ {ev(node["order"])} {ev(node["arg"])})'
    if op == 'bessel_cross':
        n, m = node['orders']
        s, t = node['args']
        j = lambda order, arg: ev({'op': 'bessel_j', 'order': order, 'arg': arg})
        y = lambda order, arg: ev({'op': 'bessel_y', 'order': order, 'arg': arg})
        return f'({j(n, s)} * {y(m, t)} - {y(n, s)} * {j(m, t)})'
    if op == 'deriv':
        index = len(names)
        while f'd{index}' in names.values():
            index += 1
        bound = f'd{index}'
        body = lean_expr(node['arg'], {**names, node['var']:bound}, types)
        return f'(deriv (fun ({bound} : ℝ) => {body}) {names[node["var"]]})'
    if op == 'neg': return f'(-{ev(node["arg"])})'
    if op in {'add', 'sub', 'mul', 'div'}:
        return '(' + ev(node['args'][0]) + {'add':' + ', 'sub':' - ', 'mul':' * ', 'div':' / '}[op] + ev(node['args'][1]) + ')'
    if op == 'pow': return f'({ev(node["base"])} ^ {node["exponent"]})'
    if op == 'rpow': return f'Real.rpow {ev(node["base"])} {ev(node["exponent"])}'
    if op in {'gamma', 'exp'}: return f'({"Real.Gamma" if op == "gamma" else "Real.exp"} {ev(node["arg"])})'
    if op == 'integral':
        bound = f'b{len(names)}'
        body = lean_expr(node['body'], {**names, node['var']: bound}, types)
        if node['upper'] == {'op':'infinity'}:
            return f'(∫ {bound} in Set.Ioi {ev(node["lower"])}, {body})'
        return f'(∫ {bound} in {ev(node["lower"])}..{ev(node["upper"])}, {body})'
    raise InputError('This expression has no registered full real Lean translation.')


def _condition(atom, names, types=None):
    types = types or {}
    from .real_bessel import RELATIONS
    relation = RELATIONS[atom['relation']].replace('!=', '≠').replace('>=', '≥').replace('<=', '≤')
    if atom['op'] == 'degree_compare':
        return f'{names[atom["lhs"]]} {relation} {names[atom["rhs"]]}'
    if atom['op'] == 'compare':
        p, q = atom['value']['numerator'], atom['value']['denominator']
        value = lean_expr({'op':'var','name':atom['variable']}, names, types)
        return f'{value} {relation} ({p} / {q} : ℝ)'
    return f'{lean_expr(atom["lhs"], names, types)} {relation} (0 : ℝ)'


def _recipe(recipe, lhs, rhs, names, types=None):
    types = types or {}
    if recipe == 'ring': return ['ring']
    match = match_identity(lhs, rhs)
    if not match or match['recipe'] != recipe:
        raise InputError('This recipe does not match the exact equality endpoints.')
    if recipe in bessel_y_formal.RECIPES:
        return bessel_y_formal.proof_lines(match, names, lambda a: lean_expr(a, names, types))
    if recipe in bessel_y_integer.RECIPES:
        return bessel_y_integer.proof_lines(match, names, lambda a: lean_expr(a, names, types))
    if recipe in cross_complete.RECIPES:
        return cross_complete.proof_lines(match, names, lambda a: lean_expr(a, names, types))
    if recipe in orthogonal.RECIPES:
        return orthogonal.proof_lines(match, names, lambda a: lean_expr(a, names, types))
    if recipe in classical.RECIPES:
        return classical.proof_lines(match, names, lambda a: lean_expr(a, names, types))
    args = ' '.join(lean_expr(a, names, types) for a in match['arguments'])
    hypotheses = ' '.join('(by linarith)' for _ in match['arguments'])
    fact = f'SpecialFunctionProofAgent.{recipe} {args} {hypotheses}'
    if match['reverse']: fact = f'({fact}).symm'
    return [f'simpa only [neg_mul, Real.rpow_eq_pow] using ({fact})']


def render(data):
    from .research_proof import is_research, render as render_research
    if is_research(data):
        return render_research(data)
    validate_proof(data)
    names = {name: f'v{i}' for i, name in enumerate(sorted(data['variables']))}
    types = data['variables']
    allowed_types = {'real', 'nat', 'int'} if bessel_y_integer.complete_target(data) else {'real', 'nat'}
    if any(kind not in allowed_types for kind in types.values()):
        raise InputError('Integer degree is supported only for registered integer-Y identities; polynomial degrees remain natural.')
    binders = ' '.join(f'({names[n]} : {dict(real="ℝ", nat="ℕ", int="ℤ")[types[n]]})' for n in sorted(names))
    conditions = ' '.join(f'(h{i} : {_condition(a, names, types)})' for i,a in enumerate(data['assumptions']))
    proposition = f'{lean_expr(data["lhs"], names, types)} = {lean_expr(data["rhs"], names, types)}'
    lines = ['import SpecialFunctionProofAgent', '', 'open scoped Real', 'open MeasureTheory', '',
             'namespace BesselAgentCandidate', '', f'theorem target {binders} {conditions} : {proposition} := by']
    # Derive integer comparisons from the fixed real-valued rational bounds. This
    # preserves Nat's discreteness (n>0, n>=1/2, and n!=0 all imply n>=1).
    from .real_bessel import RELATIONS
    for i, atom in enumerate(data['assumptions']):
        if atom['op'] != 'compare' or types[atom['variable']] != 'nat':
            continue
        p, q = atom['value']['numerator'], atom['value']['denominator']
        v = names[atom['variable']]
        relation = RELATIONS[atom['relation']].replace('!=', '≠').replace('>=', '≥').replace('<=', '≤')
        lines += [f'  have hn_condition_{i} : ({q} : ℤ) * ({v} : ℤ) {relation} ({p} : ℤ) := by',
                  f'    have hr : ({q} : ℝ) * ({v} : ℝ) {relation} ({p} : ℝ) := by']
        lines += [f'      intro hz; apply h{i}; linarith' if atom['relation'] == 'ne' else f'      linarith [h{i}]',
                  '    exact_mod_cast hr']
    proof = data['proof']
    if proof['mode'] == 'direct':
        lines += ['  '+line for line in _recipe(proof['recipe'], data['lhs'], data['rhs'], names, types)]
    elif proof['mode'] == 'steps':
        for i,step in enumerate(proof['steps']):
            lines += [f'  have step_{i+1} : {lean_expr(step["before"], names, types)} = {lean_expr(step["after"], names, types)} := by']
            lines += ['    '+line for line in _recipe(step['recipe'], step['before'], step['after'], names, types)]
        chain = 'step_1'
        for i in range(1,len(proof['steps'])): chain = f'({chain}).trans step_{i+1}'
        lines += [f'  exact {chain}']
    else: raise InputError('Diagnostic mode has no full Lean certificate.')
    lines += ['', 'end BesselAgentCandidate', '', '#eval IO.println "BESSEL_AUDIT_BEGIN"',
              '#print axioms BesselAgentCandidate.target', '#eval IO.println "BESSEL_AUDIT_END"', '']
    return '\n'.join(lines)


def verify(data, output_dir, timeout):
    from .real_bessel import display, labels, domains, _walk
    from .real_numeric import diagnose
    from . import research_proof
    research = research_proof.is_research(data)
    numeric = diagnose({key: value for key, value in data.items() if key != 'proof'} if research else data)
    analysis = match_identity(data['lhs'], data['rhs'])
    dependencies = research_proof.inspect_dependencies(data) if research else None
    if research:
        analysis = {'recipe': 'research', 'dependencies': dependencies}
    result = {'status':'unresolved', 'reason':'no_accepted_full_certificate',
              'statement':display(data['lhs'])+' = '+display(data['rhs']), 'conditions':labels(data),
              'environment':environment(), 'conventions':conventions(data), 'full_function_proof':False,
              'analysis':analysis, 'numerical':numeric, 'attempts':[],
              'request_sha256':_sha((output_dir/'request.json').read_bytes())}
    bessel_scope = (cross_complete.FORMAL_SCOPE if cross_complete.complete_target(data) else
                    bessel_y_integer.formal_scope(data) if bessel_y_integer.complete_target(data) else
                    bessel_y_formal.FORMAL_SCOPE if bessel_y_formal.contains(data) else None)
    if bessel_scope:
        result['full_bessel_proof'] = False
        result['formal_scope'] = bessel_scope
    if research:
        result['formal_scope'] = research_proof.FORMAL_SCOPE
        result['research_dependencies'] = dependencies
    bounds = domains(data)
    pending = []
    if analysis and analysis['recipe'] in {'gamma_recurrence', 'beta_integral', 'gamma_scaled_integral'}:
        for arg in analysis['arguments']:
            lo = bounds[arg['name']][0]
            if not lo or not (lo[0] > 0 or lo == (0, True)): pending.append(arg['name']+' > 0')
    # Reject direct special-function singularities even when used in a ring identity.
    from .real_bessel import _positive, domain_obligations
    # This exact root recipe proves positivity/nonzero of both denominators
    # from the original scalar bounds and root condition in the Lean source.
    derived = {'id': 'cross_product_root_fraction'} if cross_complete.complete_target(data) else None
    pending += domain_obligations(data, derived)
    for node in _walk([data['lhs'], data['rhs']]):
        if node.get('op') == 'gamma' and not _positive(node['arg'], bounds):
            pending.append(display(node['arg'])+' > 0')
    if pending:
        result.update(status='needs_conditions', reason='domain_conditions_required', pending_domain_conditions=sorted(set(pending)))
    elif data['proof']['mode'] != 'diagnostic':
        try:
            source = render(data)
        except InputError as exc:
            result['reason'] = str(exc)
        else:
            path = output_dir/'proof_attempt.lean'
            path.write_text(source, encoding='utf-8')
            checked = _run_lean(path, timeout)
            result['attempts'].append(checked)
            if checked['accepted']:
                (output_dir/'certificate.lean').write_text(source, encoding='utf-8')
                result.update(status='proved', reason='full_lean_certificate', full_function_proof=True,
                              certificate_kind='proof', certificate_sha256=_sha(source.encode()))
    if bessel_scope:
        result['full_bessel_proof'] = result['full_function_proof']
    _save_json(output_dir/'analysis.json', analysis or {'status':'no_matching_template'})
    _save_json(output_dir/'numerical.json', numeric)
    _save_json(output_dir/'result.json', result)
    lines = ['# Special Function Proof Agent', '', result['statement'], '', '条件：'+'、'.join(labels(data)), '',
             '完全Lean証明：'+result['status'], '数値診断：'+numeric['diagnostic']]
    if research:
        lines += ['', '研究補題の再利用：元の命題と全条件を固定し、各補題の仮定をこの命題の条件からLeanで確認します。']
        for dependency in dependencies:
            lines += [f'- {dependency["name"]} ({dependency["id"]})',
                      '  '+dependency['statement'], '  補題の条件：'+'、'.join(dependency['conditions'])]
        applications = ([data['proof']['uses']] if data['proof']['mode'] == 'direct' else
                        [step['uses'] for step in data['proof']['steps']])
        application_index = 0
        for uses in applications:
            for use in uses:
                application_index += 1
                arguments = '、'.join(name+' ← '+display(value) for name, value in use['arguments'].items())
                lines += [f'適用{application_index}：{use["lemma"]}、{arguments}。'+('右辺から左辺へ使います。' if use['reverse'] else '左辺から右辺へ使います。')]
        lines += ['証明と依存関係は certificate.lean、request.json、analysis.json に保存します。']
    from .real_bessel import _walk
    if any(node.get('op') in {'hermite_h', 'hermite_he'} for node in _walk([data['lhs'], data['rhs']])):
        lines += ['', 'Hermite規約：Hは物理学規約、Heは確率論規約。次数は自然数です。']
    if bessel_y_integer.complete_target(data):
        lines += ['', '整数Y規約：正実軸の標準次数微分式besselYIntを用います。J級数の局所一様収束から次数微分可能性と非整数Yの整数次数極限を証明しています。']
        if analysis['recipe'] in {'integer_y_derivative', 'integer_y_wronskian'}:
            lines += [bessel_y_integer.REASONS[analysis['recipe']]]
    if cross_complete.complete_target(data):
        lines += ['', '交差積規約：X_nm(s,t)=J_n(s)*Y_m(t)-Y_n(s)*J_m(t)。', cross_complete.REASONS['cross_product_root']]
    if data['proof']['mode'] == 'steps':
        lines += ['', '構造化ステップ（各等式を元の全条件で検査）：']
        for i,step in enumerate(data['proof']['steps'],1):
            lines += [f'{i}. {display(step["before"])} = {display(step["after"])}', '   '+step['reason']]
    (output_dir/'report.md').write_text('\n'.join(lines)+'\n', encoding='utf-8')
    return result


def replay(data, result, output_dir, timeout):
    from . import research_proof
    research = research_proof.is_research(data)
    if result.get('status') != 'proved' or result.get('full_function_proof') is not True:
        raise InputError('This run has no full special-function certificate.')
    if result.get('certificate_kind') != 'proof':
        raise InputError('Certificate kind and full proof status disagree.')
    bessel_scope = (cross_complete.FORMAL_SCOPE if cross_complete.complete_target(data) else
                    bessel_y_integer.formal_scope(data) if bessel_y_integer.complete_target(data) else
                    bessel_y_formal.FORMAL_SCOPE if bessel_y_formal.contains(data) else None)
    if bessel_scope and result.get('full_bessel_proof') is not True:
        raise InputError('The Bessel proof status disagrees with the full certificate.')
    if bessel_scope is None and 'full_bessel_proof' in result:
        raise InputError('The saved Bessel flag differs from the fixed proof scope.')
    if not research and result.get('formal_scope') != bessel_scope:
        raise InputError('The saved formal scope differs from the fixed target.')
    if research:
        dependencies = research_proof.inspect_dependencies(data)
        analysis = {'recipe': 'research', 'dependencies': dependencies}
        from .core import load_json
        if (result.get('formal_scope') != research_proof.FORMAL_SCOPE or
                result.get('research_dependencies') != dependencies or
                result.get('analysis') != analysis or load_json(output_dir/'analysis.json') != analysis):
            raise InputError('Saved research dependencies or scope changed.')
    source = render(data)
    certificate = output_dir/'certificate.lean'
    if result.get('environment') != environment() or result.get('conventions') != conventions(data):
        raise InputError('The mathematical environment or conventions changed.')
    if certificate.read_text(encoding='utf-8') != source or result.get('certificate_sha256') != _sha(source.encode()):
        raise InputError('Saved certificate differs from the fixed target and recipe.')
    if result.get('request_sha256') != _sha((output_dir/'request.json').read_bytes()):
        raise InputError('The saved request changed.')
    checked = _run_lean(certificate, timeout)
    return {'status':'proved' if checked['accepted'] else 'unresolved', 'replayed':checked['accepted'], 'verification':checked, **({'full_bessel_proof': checked['accepted']} if bessel_scope else {})}
