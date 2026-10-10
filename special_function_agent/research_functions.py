"""Finite real research definitions, simultaneous expansion, and safe Lean declarations."""
from __future__ import annotations

from copy import deepcopy
import json
import re

from .core import InputError, _keys, _sha
from . import real_bessel, real_special

MAX_DEFINITIONS = 12
MAX_DEPTH = 4
MAX_BYTES = 256 * 1024
_FIELDS = {'schema_version', 'name', 'parameters', 'body', 'definitions'}
_ID = re.compile(r'[0-9a-f]{64}\Z')
_RESERVED = {name.casefold() for name in real_bessel.RESERVED_NAMES} | {
    'def', 'theorem', 'axiom', 'namespace', 'end', 'by', 'sorry', 'let', 'fun', 'match',
    'real', 'nat', 'integer', 'defined', 'deriv', 'integral', 'rpow', 'besselagentcandidate'}


def _json(value):
    try:
        raw = json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(',', ':'), allow_nan=False).encode('utf-8')
    except (ValueError, TypeError, UnicodeError, RecursionError) as exc:
        raise InputError('Research definitions require bounded finite UTF-8 JSON.') from exc
    if len(raw) > MAX_BYTES:
        raise InputError('Research definitions exceed the 256 KiB limit.')
    return raw


def _copy(value):
    try:
        return deepcopy(value)
    except RecursionError as exc:
        raise InputError('Research definitions exceed the supported nesting depth.') from exc


def _name(name):
    return (real_bessel.is_variable_name(name) and name.casefold() not in _RESERVED
            and not name.casefold().startswith('researchfunction_'))


def _calls(value):
    return {node.get('function') for node in real_bessel._walk(value) if node.get('op') == 'defined'
            and isinstance(node.get('function'), str)}


def contains(data):
    """Recognize calls in the active target/plan, excluding saved lemma evidence."""
    if isinstance(data, dict):
        return ('definitions' in data or data.get('op') == 'defined'
                or any(contains(value) for key, value in data.items() if key not in {'lemmas', 'evidence', 'manifest'}))
    return isinstance(data, list) and any(contains(value) for value in data)


def _finite(node, variables, depth=0, budget=None):
    """Type-check finite expressions; mathematical domains are checked on use."""
    budget = [1200] if budget is None else budget
    budget[0] -= 1
    if depth > 24 or budget[0] < 0 or not isinstance(node, dict):
        raise InputError('A research definition exceeds the expression size or depth limit.')
    op = node.get('op')
    if not isinstance(op, str): raise InputError('Every finite expression requires an operation string.')
    child = lambda value: _finite(value, variables, depth+1, budget)
    if op == 'var':
        _keys(node, {'op', 'name'})
        if not real_bessel.is_variable_name(node['name']) or node['name'] not in variables or variables[node['name']] != 'real':
            raise InputError('Definition variables must be declared real parameters.')
    elif op == 'int':
        _keys(node, {'op', 'value'})
        if type(node['value']) is not int or abs(node['value']) > 1000:
            raise InputError('Integer literals must be between -1000 and 1000.')
    elif op == 'pi':
        _keys(node, {'op'})
    elif op in {'neg', 'gamma', 'exp', 'erf', 'sqrt'}:
        _keys(node, {'op', 'arg'}); child(node['arg'])
    elif op in {'add', 'sub', 'mul', 'div'}:
        _keys(node, {'op', 'args'})
        if not isinstance(node['args'], list) or len(node['args']) != 2:
            raise InputError('A finite binary operation requires two arguments.')
        for item in node['args']: child(item)
    elif op in {'pow', 'rpow'}:
        _keys(node, {'op', 'base', 'exponent'}); child(node['base'])
        if op == 'rpow': child(node['exponent'])
        elif type(node['exponent']) is not int or not 0 <= node['exponent'] <= 12:
            raise InputError('Finite natural powers range from zero to twelve.')
    elif op in real_bessel.POLYNOMIAL_OPS | {'bessel_j', 'bessel_y', 'bessel_y_noninteger', 'bessel_cross'}:
        # Reuse the existing degree/type grammar with harmless scalar arguments.
        view = _copy(node)
        if op == 'bessel_cross':
            _keys(node, {'op', 'orders', 'args'})
            if not isinstance(node['args'], list) or len(node['args']) != 2:
                raise InputError('A cross product requires two real arguments.')
            for item in node['args']: child(item)
            view['args'] = [{'op': 'int', 'value': 1}]*2
            orders = node['orders']
        else:
            parameters = {'alpha', 'beta'} if op == 'jacobi' else {'alpha'} if op == 'laguerre' else set()
            _keys(node, {'op', 'order', 'arg'} | parameters)
            for key in {'arg'} | parameters:
                child(node[key]); view[key] = {'op': 'int', 'value': 1}
            orders = [node['order']]
        if any(item.get('op') in ('var', 'defined') for item in real_bessel._walk(orders)):
            raise InputError('Research definitions use fixed natural/integer degrees.')
        real_bessel._validate_expr(view, {})
        real_special.lean_expr(view, {}, {})
    else:
        raise InputError('Definition bodies and call arguments use finite existing real expressions; derivatives, integrals and infinity are excluded.')


def _substitute(node, arguments, budget=None):
    budget = [1200] if budget is None else budget
    budget[0] -= 1
    if budget[0] < 0:
        raise InputError('Simultaneous substitution exceeds the expression size limit.')
    if isinstance(node, dict):
        if node.get('op') == 'var' and node.get('name') in arguments:
            return _substitute(arguments[node['name']], {}, budget)
        return {key: _substitute(value, arguments, budget) for key, value in node.items()}
    if isinstance(node, list): return [_substitute(item, arguments, budget) for item in node]
    return node


def _expand(node, infos, variables=None, depth=0, budget=None):
    budget = [1200] if budget is None else budget
    budget[0] -= 1
    if depth > 24 or budget[0] < 0:
        raise InputError('Expanded research expressions exceed the supported size or depth.')
    if isinstance(node, list): return [_expand(item, infos, variables, depth+1, budget) for item in node]
    if not isinstance(node, dict): return node
    if node.get('op') == 'rational':
        from .core import _fixed_exponent
        _fixed_exponent(node)
        return {'op': 'div', 'args': [{'op': 'int', 'value': node['numerator']},
                                    {'op': 'int', 'value': node['denominator']}]}
    if node.get('op') == 'defined':
        _keys(node, {'op', 'function', 'arguments'})
        key, arguments = node['function'], node['arguments']
        if not isinstance(key, str) or key not in infos:
            raise InputError('A research call must reference an included definition ID.')
        info = infos[key]
        if not isinstance(arguments, dict) or set(arguments) != set(info['snapshot']['parameters']):
            raise InputError('A research call must supply exactly every real parameter.')
        if any(item.get('op') in ('deriv', 'integral', 'infinity') for item in real_bessel._walk(arguments)):
            raise InputError('Research call arguments exclude derivatives, integrals and infinity.')
        expanded = {name: _expand(value, infos, variables, depth+1, budget) for name, value in arguments.items()}
        for value in expanded.values():
            scope = variables if variables is not None else _expression_variables(value)
            _finite(value, scope)
        result = _substitute(info['expanded'], expanded)
        _json(result)
        # Recheck the expanded size, including copies introduced by substitution.
        scope = variables if variables is not None else _expression_variables(result)
        _finite(result, scope)
        return result
    if any(_calls(node.get(field)) for field in ('order', 'orders')):
        raise InputError('A real research function cannot supply a natural or integer degree.')
    result = {}
    for key, value in node.items():
        if key in {'order', 'orders'}:
            result[key] = _copy(value)
            continue
        scope = variables
        if node.get('op') == 'integral' and key == 'body' and variables is not None and isinstance(node.get('var'), str):
            scope = {**variables, node['var']: 'real'}
        result[key] = _expand(value, infos, scope, depth+1, budget)
    return result


def _definition(snapshot, context, depth):
    _keys(snapshot, _FIELDS | {'id'})
    _json(snapshot)
    key = snapshot['id']
    if not isinstance(key, str) or not _ID.fullmatch(key) or key != _sha(_json({k: v for k, v in snapshot.items() if k != 'id'})):
        raise InputError('The research definition ID differs from its meaning.')
    if depth > MAX_DEPTH or key in context['active']:
        raise InputError('Research definitions exceed depth four or contain a cycle.')
    if key in context['infos']:
        info = context['infos'][key]
        if depth + info['height'] - 1 > MAX_DEPTH:
            raise InputError('Research definitions exceed depth four.')
        return info
    if type(snapshot['schema_version']) is not int or snapshot['schema_version'] != 1 or not _name(snapshot['name']):
        raise InputError('Use definition schema version 1 and an unreserved safe ASCII name.')
    folded = snapshot['name'].casefold()
    if folded in context['names'] and context['names'][folded] != key:
        raise InputError('Distinct research definitions must have distinct names.')
    parameters = snapshot['parameters']
    if (not isinstance(parameters, dict) or not 1 <= len(parameters) <= 3
            or any(not real_bessel.is_variable_name(name) or kind != 'real' for name, kind in parameters.items())
            or folded in {name.casefold() for name in parameters}
            or len({name.casefold() for name in parameters}) != len(parameters)):
        raise InputError('A definition needs one to three distinct real parameters, separate from its name.')
    context['names'][folded] = key
    context['active'].add(key)
    if len(context['names']) > MAX_DEFINITIONS:
        raise InputError('At most twelve research definitions may occur in a dependency closure.')
    dependencies = snapshot['definitions']
    if not isinstance(dependencies, list) or len(dependencies) > MAX_DEFINITIONS:
        raise InputError('Definition dependencies must be a list of at most twelve snapshots.')
    children = [_definition(item, context, depth+1) for item in dependencies]
    ids = [info['snapshot']['id'] for info in children]
    if len(set(ids)) != len(ids) or set(ids) != _calls(snapshot['body']):
        raise InputError('Definition dependencies must be distinct and exactly the IDs called in its body.')
    allowed = {key: value for child in children for key, value in child['closure'].items()}
    if any(item.get('op') in ('deriv', 'integral', 'infinity') for item in real_bessel._walk(snapshot['body'])):
        raise InputError('Research definition bodies exclude derivatives, integrals and infinity.')
    expanded = _expand(snapshot['body'], allowed, parameters)
    _finite(expanded, parameters)
    info = {'snapshot': snapshot, 'expanded': expanded,
            'height': 1 + max((item['height'] for item in children), default=0), 'closure': allowed}
    info['closure'] = {**allowed, key: info}
    context['active'].remove(key)
    context['infos'][key] = info
    return info


def _definitions(definitions):
    _json(definitions)
    if not isinstance(definitions, list) or len(definitions) > MAX_DEFINITIONS:
        raise InputError('Select at most twelve research definition snapshots.')
    context = {'infos': {}, 'active': set(), 'names': {}}
    roots = [_definition(item, context, 1) for item in definitions]
    if len({info['snapshot']['id'] for info in roots}) != len(roots):
        raise InputError('Selected research definition IDs must be distinct.')
    for info in context['infos'].values():
        if any(name.casefold() in context['names'] for name in info['snapshot']['parameters']):
            raise InputError('Research parameter names must be distinct from selected function names.')
    return context['infos']


def make_definition(rawWithoutId):
    _keys(rawWithoutId, _FIELDS)
    snapshot = {**rawWithoutId, 'id': _sha(_json(rawWithoutId))}
    return _copy(validate_definition(snapshot))


def validate_definition(snapshot):
    _definitions([snapshot])
    return snapshot


def expand_expr(node, definitions):
    """Expand calls by simultaneous substitution into binder-free definition bodies."""
    _json(node)
    return _expand(node, _definitions(definitions))


def _expression_variables(node):
    return {item['name']: 'real' for item in real_bessel._walk(node)
            if item.get('op') == 'var' and isinstance(item.get('name'), str)}


def expand_target(data):
    """Expand active expressions and step labels while preserving stored lemma snapshots."""
    _json(data)
    if len((json.dumps(data, ensure_ascii=False, indent=2, allow_nan=False)+'\n').encode('utf-8')) > MAX_BYTES:
        raise InputError('A saved research-function target exceeds the 256 KiB limit.')
    _keys(data, {'schema_version', 'variables', 'assumptions', 'lhs', 'rhs', 'definitions'}, {'proof'})
    if type(data['schema_version']) is not int or data['schema_version'] != 2:
        raise InputError('Research function targets require schema version 2.')
    infos = _definitions(data['definitions'])
    if not isinstance(data['variables'], dict) or any(kind != 'real' for kind in data['variables'].values()):
        raise InputError('Research function targets require all free variables to be real.')
    function_names = {info['snapshot']['name'].casefold() for info in infos.values()}
    if any(not isinstance(name, str) or name.casefold() in function_names for name in data['variables']):
        raise InputError('Target variables must be distinct from research function names.')
    for node in real_bessel._walk([data['lhs'], data['rhs'], data['assumptions'], data.get('proof', {}).get('steps', [])] if isinstance(data.get('proof', {}), dict) else []):
        if node.get('op') in ('integral', 'deriv') and isinstance(node.get('var'), str) and node['var'].casefold() in function_names:
            raise InputError('Calculus bindings must be distinct from research function names.')
    result = _copy({key: value for key, value in data.items() if key != 'definitions'})
    for key in ('lhs', 'rhs'): result[key] = _expand(data[key], infos, data['variables'])
    if not isinstance(data['assumptions'], list): raise InputError('Target assumptions must be a list.')
    for atom in result['assumptions']:
        if isinstance(atom, dict) and atom.get('op') == 'expr_compare':
            _keys(atom, {'op', 'lhs', 'relation', 'rhs'})
            atom['lhs'] = _expand(atom['lhs'], infos, data['variables'])
    real_bessel.validate({key: value for key, value in result.items() if key != 'proof'}, require_proof=False)
    proof = result.get('proof')
    if isinstance(proof, dict):
        steps = proof.get('steps', [])
        if not isinstance(steps, list): raise InputError('Proof steps must be a list.')
        before = data['lhs']
        original_labels = real_bessel.labels(data)
        label_map = dict(zip(original_labels, real_bessel.labels(result)))
        for step in steps:
            if not isinstance(step, dict) or step.get('before') != before or 'after' not in step:
                raise InputError('Definition proof steps must preserve the original consecutive endpoints.')
            before = step['after']
            labels = step.get('conditions')
            if not isinstance(labels, list) or any(not isinstance(label, str) or label not in original_labels for label in labels):
                raise InputError('Step conditions must come from the original target.')
            step['conditions'] = [label_map[label] for label in labels]
            for key in ('before', 'after'): step[key] = _expand(step[key], infos, data['variables'])
        if steps and before != data['rhs']:
            raise InputError('The last definition proof step must reach the original right side.')
        for holder in [proof, *steps]:
            uses = holder.get('uses', [])
            if not isinstance(uses, list): raise InputError('Research lemma uses must be a list.')
            for use in uses:
                if not isinstance(use, dict) or not isinstance(use.get('arguments'), dict):
                    raise InputError('Research lemma arguments must be an object.')
                use['arguments'] = {name: _expand(value, infos, data['variables']) for name, value in use['arguments'].items()}
    _json(result)
    return result


def validate_target(data, require_proof=True):
    from . import research_proof
    expanded = expand_target(data)
    real_bessel.validate({key: value for key, value in expanded.items() if key != 'proof'}, require_proof=False)
    if require_proof and 'proof' not in expanded:
        raise InputError('A research-function target requires a closed proof plan.')
    if 'proof' in expanded:
        if research_proof.is_research(expanded): research_proof.validate_proof(expanded)
        else: real_special.validate_proof(expanded)
    return data


def _lean_name(key):
    return 'ResearchFunction_'+key


def _lean(node, names, types, infos):
    if node['op'] == 'defined':
        info = infos[node['function']]
        args = ' '.join('('+_lean(node['arguments'][name], names, types, infos)+')'
                        for name in sorted(info['snapshot']['parameters']))
        return '('+_lean_name(node['function'])+' '+args+')'
    if node['op'] in {'deriv', 'integral'}:
        prefix = 'd' if node['op'] == 'deriv' else 'b'
        index = len(names)
        while prefix+str(index) in names.values(): index += 1
        bound = prefix+str(index)
        mapping = {**names, node['var']: bound}
        if node['op'] == 'deriv':
            body = _lean(node['arg'], mapping, types, infos)
            return f'(deriv (fun ({bound} : ℝ) => {body}) {names[node["var"]]})'
        body = _lean(node['body'], mapping, {**types, node['var']: 'real'}, infos)
        lower = _lean(node['lower'], names, types, infos)
        if node['upper'] == {'op': 'infinity'}: return f'(∫ {bound} in Set.Ioi {lower}, {body})'
        return f'(∫ {bound} in {lower}..{_lean(node["upper"], names, types, infos)}, {body})'
    # Reuse the standard renderer for each ordinary node; child renderings retain
    # the lexical binder map and remain verifier-owned Lean expressions.
    view, mapping = _copy(node), dict(names)
    for field in ('arg', 'args', 'base', 'alpha', 'beta', 'exponent'):
        if field not in node or not isinstance(node[field], (dict, list)): continue
        values = node[field] if isinstance(node[field], list) else [node[field]]
        replacements = []
        for value in values:
            name = '__research_child_'+str(len(mapping))
            while name in mapping: name += '_'
            mapping[name] = _lean(value, names, types, infos)
            replacements.append({'op': 'var', 'name': name})
        view[field] = replacements if isinstance(node[field], list) else replacements[0]
    rendered = real_special.lean_expr(view, mapping, types)
    return '('+rendered+')' if node['op'] == 'rpow' else rendered


def lean_expr(node, names, types, definitions):
    infos = _definitions(definitions)
    expanded = _expand(node, infos, types)
    real_bessel._validate_expr(expanded, types)
    return _lean(node, names, types, infos)


def lean_definitions(definitions):
    infos = _definitions(definitions)
    lines = []
    for key, info in infos.items():
        definition = info['snapshot']
        names = {name: 'p'+str(index) for index, name in enumerate(sorted(definition['parameters']))}
        binders = ' '.join(f'({names[name]} : ℝ)' for name in sorted(names))
        body = _lean(definition['body'], names, definition['parameters'], infos)
        lines.append(f'noncomputable def {_lean_name(key)} {binders} : ℝ := {body}')
    return '\n\n'.join(lines)


def metadata(definitions):
    return [{'id': key, 'name': info['snapshot']['name'], 'parameters': _copy(info['snapshot']['parameters']),
             'dependencies': [item['id'] for item in info['snapshot']['definitions']], 'lean_name': _lean_name(key)}
            for key, info in _definitions(definitions).items()]


def definition_conventions(snapshot):
    from .registry import conventions
    infos = _definitions([snapshot])
    return conventions({'lhs': [info['expanded'] for info in infos.values()]})


def render_definition(snapshot):
    infos = _definitions([snapshot])
    definition = infos[snapshot['id']]
    names = {name: 'v'+str(index) for index, name in enumerate(sorted(snapshot['parameters']))}
    binders = ' '.join(f'({names[name]} : ℝ)' for name in sorted(names))
    arguments = ' '.join(names[name] for name in sorted(names))
    expanded = _lean(definition['expanded'], names, snapshot['parameters'], infos)
    return ('import SpecialFunctionProofAgent\n\nopen scoped Real\nopen MeasureTheory\n\n'
            +lean_definitions([snapshot])+'\n\nnamespace BesselAgentCandidate\n\n'
            +f'theorem target {binders} : {_lean_name(snapshot["id"])} {arguments} = {expanded} := by\n  rfl\n'
            +'\nend BesselAgentCandidate\n\n#eval IO.println "BESSEL_AUDIT_BEGIN"\n'
            +'#print axioms BesselAgentCandidate.target\n#eval IO.println "BESSEL_AUDIT_END"\n')
