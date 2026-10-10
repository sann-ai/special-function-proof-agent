"""Closed real J/Y/cross-product targets with explicitly scoped diagnostics.

Version 2 never promotes numerical or conditional algebraic evidence to a proof
of a theorem about Bessel Y. Version 1 keeps its existing Lean semantics.
"""
from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import json
import re
from typing import Any

from .core import InputError, NeedsConditions, _keys, _expr, _constant, _run_lean, _save_json, _sha, environment, load_json

VARIABLES = {'n', 'x', 'z', 'lambda', 's', 'w', 't'}
POLYNOMIAL_OPS = {'hermite_h', 'hermite_he', 'legendre', 'laguerre', 'jacobi'}
RESERVED_NAMES = {'J', 'Y', 'X', 'H', 'He', 'P', 'L', 'Legendre', 'Laguerre', 'Jacobi', 'YNoninteger', 'Gamma', 'gamma', 'exp', 'erf', 'pi', 'sqrt', 'int',
                  'infinity', 'inf', 'D', 'Dx', 'Dt', 'd'}
RELATIONS = {'gt': '>', 'ge': '>=', 'lt': '<', 'le': '<=', 'eq': '=', 'ne': '!='}
CROSS_DEFINITION = 'X_nm(s,t) = J_n(s)*Y_m(t) - Y_n(s)*J_m(t)'
TEMPLATE = Path(__file__).with_name('templates') / 'cross_product.lean'


def is_variable_name(name):
    return isinstance(name, str) and re.fullmatch(r'[A-Za-z][A-Za-z0-9_]{0,31}', name) is not None and name not in RESERVED_NAMES


def is_extended(data: Any) -> bool:
    return isinstance(data, dict) and type(data.get('schema_version')) is int and data['schema_version'] == 2


def _walk(node):
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from _walk(value)
    elif isinstance(node, list):
        for value in node:
            yield from _walk(value)


def _convert(node):
    from .parser import _order
    op = node['op']
    if op in {'int', 'var'}:
        return node
    if op in {'add', 'sub', 'mul', 'div'}:
        return {'op': op, 'args': [_convert(a) for a in node['args']]}
    if op == 'neg':
        return {'op': op, 'arg': _convert(node['arg'])}
    if op in {'gamma', 'exp', 'erf', 'sqrt'}:
        return {'op': op, 'arg': _convert(node['arg'])}
    if op in {'infinity', 'pi'}:
        return {'op': op}
    if op == 'deriv':
        arg = _convert(node['arg'])
        variable = node.get('variable')
        if variable is None:
            names = _free_names(arg) - {'n'}
            if len(names) != 1:
                raise NeedsConditions('Specify the differentiation variable as D_x(expression).')
            variable = next(iter(names))
        return {'op': op, 'var': variable, 'arg': arg}
    if op == 'integral':
        return {'op': op, 'var': node['variable'], 'lower': _convert(node['lower']),
                'upper': _convert(node['upper']), 'body': _convert(node['arg'])}
    if op in {'bessel_j', 'bessel_y', 'bessel_y_noninteger'} | POLYNOMIAL_OPS:
        return {'op': op, 'order': _order(node['order']), 'arg': _convert(node['arg']),
                **{p: _convert(node[p]) for p in ('alpha', 'beta') if p in node}}
    if op == 'bessel_cross':
        return {'op': op, 'orders': [_order(a) for a in node['orders']], 'args': [_convert(a) for a in node['args']]}
    if op == 'power':
        exponent = node['exponent']
        if exponent['op'] == 'int' and 0 <= exponent['value'] <= 12:
            return {'op': 'pow', 'base': _convert(node['base']), 'exponent': exponent['value']}
        return {'op': 'rpow', 'base': _convert(node['base']), 'exponent': _convert(exponent)}
    raise InputError('Unsupported real expression; use arithmetic, Gamma, exp, real powers, integrals, or Bessel J/Y/X.')


def _free_names(node, bound=frozenset()):
    if isinstance(node, list):
        return set().union(*(_free_names(item, bound) for item in node)) if node else set()
    if not isinstance(node, dict):
        return set()
    if node.get('op') == 'var':
        return {node['name']} - bound
    if node.get('op') == 'integral':
        return (_free_names(node['lower'], bound) | _free_names(node['upper'], bound)
                | _free_names(node['body'], bound | {node['var']}))
    if node.get('op') == 'deriv':
        return ({node['var']} - bound) | _free_names(node['arg'], bound)
    return set().union(*(_free_names(value, bound) for value in node.values()))


def _parts(raw):
    if isinstance(raw, list) and all(isinstance(item, str) for item in raw):
        raw = ','.join(raw)
    if not isinstance(raw, str) or not raw.strip():
        raise NeedsConditions('State the real domain, for example x > 0 or 0 < lambda < 1, z > 0.')
    if len(raw) > 8192:
        raise InputError('Conditions exceed the text length limit.')
    raw = raw.replace(r'\alpha', 'alpha').replace(r'\beta', 'beta').replace('α', 'alpha').replace('β', 'beta')
    raw = raw.replace(r'\lambda', 'lambda').replace('λ', 'lambda').replace('、', ',').replace('，', ',')
    raw = raw.replace(r'\mathbb{Z}', 'Z').replace(r'\mathbb{R}', 'R').replace(r'\mathbb{N}', 'N').replace(r'\in', 'in').replace('∈', 'in').replace('ℤ', 'Z').replace('ℝ', 'R').replace('ℕ', 'N')
    for old, new in [(r'\geq', '>='), (r'\leq', '<='), (r'\neq', '!='), (r'\ge', '>='), (r'\le', '<='), (r'\ne', '!='), ('≥', '>='), ('≤', '<='), ('≠', '!=')]:
        raw = raw.replace(old, new)
    raw = re.sub(r'\b(?:and|where|for)\b|かつ', ',', raw)
    raw = re.sub(r'\\(?:frac|dfrac|tfrac)\s*\{(-?[0-9]+)\}\s*\{([0-9]+)\}', r'\1/\2', raw)
    stack, start, parts = [], 0, []
    for i, char in enumerate(raw):
        if char in '({':
            stack.append(char)
        elif char in ')}':
            if not stack or stack.pop() != {')': '(', '}': '{'}[char]:
                raise InputError('Unbalanced condition parentheses.')
        elif char == ',' and not stack:
            parts.append(raw[start:i].strip())
            start = i + 1
    if stack:
        raise InputError('Unbalanced condition parentheses.')
    return [p for p in parts + [raw[start:].strip()] if p]


def parse_target(text, conditions):
    from .parser import _Parser
    lhs, rhs = _Parser(text, extended=True).equation()
    lhs, rhs = _convert(lhs), _convert(rhs)
    assumptions = []
    order_type = None
    real_stated = set()
    parts = [] if (conditions is None or conditions == '') and not _free_names([lhs, rhs]) else _parts(conditions)
    for part in parts:
        compact = re.sub(r'\s+', '', part)
        declared_type = ('int' if compact in {'ninteger', 'ninZ', 'n:Z', 'nは整数', 'n整数'} else
                         'nat' if compact in {'nnatural', 'ninN', 'n:N', 'nは自然数', 'n自然数'} else None)
        if declared_type:
            if order_type is not None and order_type != declared_type:
                raise InputError('Declare n with one order type: integer or natural.')
            order_type = declared_type
            continue
        real = re.fullmatch(r'([A-Za-z][A-Za-z0-9_]{0,31}?)(?:real|inR|:R|は実数)', compact)
        if real and is_variable_name(real[1]) and real[1] != 'n':
            real_stated.add(real[1])
            continue
        tokens = re.split(r'(>=|<=|!=|>|<|=)', part)
        if len(tokens) not in {3, 5}:
            raise NeedsConditions('State scalar comparisons or an expression equal/non-equal to zero.')
        for i in range(0, len(tokens)-2, 2):
            left, relation, right = (p.strip() for p in tokens[i:i+3])
            operator = next(key for key, value in RELATIONS.items() if value == relation)
            if is_variable_name(left) or is_variable_name(right):
                if is_variable_name(right):
                    left, right = right, left
                    operator = {'gt': 'lt', 'ge': 'le', 'lt': 'gt', 'le': 'ge', 'eq': 'eq', 'ne': 'ne'}[operator]
                if not re.fullmatch(r'[+-]?[0-9]+(?:/[0-9]+)?', right):
                    raise NeedsConditions('Scalar comparisons require an exact rational constant.')
                try:
                    q = Fraction(right)
                except ZeroDivisionError as exc:
                    raise NeedsConditions('A condition constant has a zero denominator.') from exc
                atom = {'op': 'compare', 'variable': left, 'relation': operator,
                        'value': {'numerator': q.numerator, 'denominator': q.denominator}}
            else:
                if operator not in {'eq', 'ne'} or right != '0' or len(tokens) != 3:
                    raise NeedsConditions('Function-value conditions have the form expression = 0 or expression != 0.')
                parser = _Parser(left, extended=True)
                expr = parser.expression()
                if parser.peek() is not None:
                    raise InputError('Unexpected token in a function-value condition.')
                atom = {'op': 'expr_compare', 'lhs': _convert(expr), 'relation': operator, 'rhs': {'op': 'int', 'value': 0}}
            if atom not in assumptions:
                assumptions.append(atom)
    names = _free_names([lhs, rhs, assumptions]) | real_stated
    names |= {a['variable'] for a in assumptions if a['op'] == 'compare'}
    if 'n' in names and order_type is None:
        raise NeedsConditions('State n integer for Bessel orders or n natural for Polynomial orders.')
    target = {'schema_version': 2, 'variables': {name: order_type if name == 'n' else 'real' for name in sorted(names)},
              'assumptions': assumptions, 'lhs': lhs, 'rhs': rhs}
    validate(target, require_proof=False)
    return target


def _polynomial_order(node, variables):
    """Validate the small natural-order grammar and return a required lower bound."""
    if not isinstance(node, dict):
        raise InputError('Polynomial orders require a natural literal or n with a small offset.')
    if node.get('op') == 'int':
        _keys(node, {'op', 'value'})
        if type(node['value']) is not int or not 0 <= node['value'] <= 1000:
            raise InputError('Literal Polynomial orders must be natural numbers bounded by 1000.')
        return 0
    if node.get('op') == 'var':
        _keys(node, {'op', 'name'})
        if node['name'] != 'n' or variables.get('n') != 'nat':
            raise InputError('Polynomial order n requires the natural-number type.')
        return 0
    if node.get('op') in {'add', 'sub'}:
        _keys(node, {'op', 'args'})
        args = node['args']
        if not isinstance(args, list) or len(args) != 2 or args[0] != {'op': 'var', 'name': 'n'}:
            raise InputError('Shifted Polynomial orders have the form n+k or n-k.')
        _polynomial_order(args[0], variables)
        if not isinstance(args[1], dict) or args[1].get('op') != 'int':
            raise InputError('A Polynomial order offset must be an integer from 0 to 12.')
        _polynomial_order(args[1], variables)
        if args[1]['value'] > 12:
            raise InputError('A Polynomial order offset must be an integer from 0 to 12.')
        return args[1]['value'] if node['op'] == 'sub' else 0
    raise InputError('Polynomial orders support natural literals, n, n+k, or n-k.')


def validate_order_domains(nodes, bounds):
    for node in _walk(nodes):
        if node.get('op') in POLYNOMIAL_OPS:
            order = node['order']
            if order.get('op') == 'sub':
                required = order['args'][1]['value']
                lower = bounds.get('n', [None, None, set()])[0]
                if lower is None or lower[0] < required:
                    raise NeedsConditions(f'The Polynomial order n-{required} requires an explicit domain implying n >= {required}.')


def _validate_expr(node, variables, depth=0, budget=None, scalar=False, bound=frozenset()):
    budget = [1200] if budget is None else budget
    budget[0] -= 1
    if depth > 24 or budget[0] < 0 or not isinstance(node, dict):
        raise InputError('Real expression exceeds the supported size or depth.')
    op = node.get('op')
    if not isinstance(op, str):
        raise InputError('Every real expression must have an op string.')
    child = lambda n, s=scalar: _validate_expr(n, variables, depth+1, budget, s, bound)
    if op == 'int':
        _keys(node, {'op', 'value'})
        if type(node['value']) is not int or abs(node['value']) > 1000:
            raise InputError('Integer literals must be between -1000 and 1000.')
    elif op == 'var':
        _keys(node, {'op', 'name'})
        if not is_variable_name(node['name']) or node['name'] not in variables and node['name'] not in bound:
            raise InputError('Every variable must have an explicit real/integer declaration.')
    elif op == 'neg':
        _keys(node, {'op', 'arg'}); child(node['arg'])
    elif op in {'add', 'sub', 'mul', 'div'}:
        _keys(node, {'op', 'args'})
        if not isinstance(node['args'], list) or len(node['args']) != 2:
            raise InputError('Binary operations require two arguments.')
        for arg in node['args']:
            child(arg)
        if op == 'div' and _constant(node['args'][1]) == 0:
            raise NeedsConditions('A denominator is identically zero.')
    elif op == 'pow':
        _keys(node, {'op', 'base', 'exponent'})
        if type(node['exponent']) is not int or not 0 <= node['exponent'] <= 12:
            raise InputError('Real diagnostics support powers 0..12.')
        child(node['base'])
    elif op == 'pi':
        _keys(node, {'op'})
    elif op in {'gamma', 'exp', 'erf', 'sqrt'}:
        _keys(node, {'op', 'arg'})
        child(node['arg'])
    elif op == 'deriv' and not scalar:
        _keys(node, {'op', 'var', 'arg'})
        name = node['var']
        if not is_variable_name(name) or variables.get(name) != 'real' or name in bound:
            raise InputError('A derivative variable must be a declared free real variable, distinct from integral bindings.')
        child(node['arg'])
    elif op == 'rpow':
        _keys(node, {'op', 'base', 'exponent'})
        child(node['base'])
        child(node['exponent'])
    elif op == 'integral' and not scalar:
        _keys(node, {'op', 'var', 'lower', 'upper', 'body'})
        name = node['var']
        if not is_variable_name(name) or name == 'n' or name in variables or name in bound:
            raise InputError('An integral variable must be a fresh real name, distinct from free variables and outer bindings.')
        child(node['lower'], True)
        if node['upper'] != {'op': 'infinity'}:
            child(node['upper'], True)
        _validate_expr(node['body'], variables, depth+1, budget, scalar, bound | {name})
    elif op == 'bessel_y_noninteger' and not scalar:
        _keys(node, {'op', 'order', 'arg'})
        from .core import _fixed_exponent
        _fixed_exponent(node['order'])
        order = node['order']
        degree = Fraction(order['numerator'], order['denominator']) if order['op'] == 'rational' else Fraction(order['value'])
        if degree not in {Fraction(-1, 2), Fraction(1, 2), Fraction(3, 2)}:
            raise InputError('YNoninteger currently supports the fixed orders -1/2, 1/2, 3/2; integer Y uses the diagnostic Y notation.')
        child(node['arg'], True)
    elif op in {'bessel_j', 'bessel_y', 'bessel_cross'} and not scalar:
        cross = op == 'bessel_cross'
        _keys(node, {'op', 'orders', 'args'} if cross else {'op', 'order', 'arg'})
        orders, args = (node['orders'], node['args']) if cross else ([node['order']], [node['arg']])
        if not isinstance(orders, list) or not isinstance(args, list) or len(orders) != (2 if cross else 1) or len(args) != len(orders):
            raise InputError('Bessel operators require the documented number of orders and arguments.')
        for order in orders:
            if isinstance(order, dict) and order.get('op') == 'rational':
                from .core import _fixed_exponent
                _fixed_exponent(order)
            else:
                _expr(order, 'int')
            if any(n.get('op') == 'var' and variables.get(n.get('name')) != 'int' for n in _walk(order)):
                raise InputError('Bessel order n requires the integer type.')
        for arg in args:
            child(arg, True)
    elif op in POLYNOMIAL_OPS and not scalar:
        parameters = ('alpha', 'beta') if op == 'jacobi' else ('alpha',) if op == 'laguerre' else ()
        _keys(node, {'op', 'order', 'arg'} | set(parameters))
        for parameter in parameters:
            child(node[parameter], True)
        _polynomial_order(node['order'], variables)
        child(node['arg'], True)
    else:
        raise InputError(f'Unsupported real diagnostic operation {op!r}.')


def domains(data):
    result = {name: [(Fraction(0), False) if kind == 'nat' else None, None, set()]
              for name, kind in data['variables'].items()}
    for atom in data['assumptions']:
        if atom['op'] != 'compare':
            continue
        domain = result[atom['variable']]
        q = Fraction(atom['value']['numerator'], atom['value']['denominator'])
        relation = atom['relation']
        if relation == 'ne':
            domain[2].add(q)
        if relation in {'gt', 'ge', 'eq'}:
            edge = q, relation == 'gt'
            if domain[0] is None or edge > domain[0]:
                domain[0] = edge
        if relation in {'lt', 'le', 'eq'}:
            edge = q, relation == 'lt'
            if domain[1] is None or (q, not edge[1]) < (domain[1][0], not domain[1][1]):
                domain[1] = edge
    for name, (lo, hi, excluded) in result.items():
        if data['variables'][name] in {'int', 'nat'}:
            if lo:
                lo = (Fraction(lo[0].numerator//lo[0].denominator+1) if lo[1] else Fraction(-(-lo[0].numerator//lo[0].denominator)), False)
            if hi:
                hi = (Fraction(-(-hi[0].numerator//hi[0].denominator)-1) if hi[1] else Fraction(hi[0].numerator//hi[0].denominator), False)
            if lo:
                while lo[0] in excluded: lo = lo[0]+1, False
            if hi:
                while hi[0] in excluded: hi = hi[0]-1, False
            result[name] = [lo, hi, excluded]
        if lo and hi and (lo[0] > hi[0] or (lo[0] == hi[0] and (lo[1] or hi[1] or lo[0] in excluded))):
            raise NeedsConditions(f'Contradictory scalar conditions for {name}.')
    return result


def validate(data, require_proof=True):
    _keys(data, {'schema_version', 'variables', 'assumptions', 'lhs', 'rhs'} | ({'proof'} if require_proof else set()), set() if require_proof else {'proof'})
    if not is_extended(data) or not isinstance(data['variables'], dict) or len(data['variables']) > 4:
        raise InputError('Version 2 permits up to four typed free variables.')
    variables = data['variables']
    if any(not is_variable_name(name) or kind not in (('int', 'nat') if name == 'n' else ('real',)) for name, kind in variables.items()):
        raise InputError('Use safe ASCII names of 1 to 32 characters for real variables; n has type int or nat. Function names are reserved.')
    if sum(kind == 'real' for kind in variables.values()) > 3:
        raise InputError('At most three free real variables are supported.')
    for side in ['lhs', 'rhs']:
        _validate_expr(data[side], variables)
    assumptions = data['assumptions']
    if not isinstance(assumptions, list) or len(assumptions) > 12:
        raise NeedsConditions('Use at most twelve explicit domain/root conditions.')
    seen = set()
    for atom in assumptions:
        if isinstance(atom, dict) and atom.get('op') == 'compare':
            _keys(atom, {'op', 'variable', 'relation', 'value'})
            if not isinstance(atom['variable'], str) or atom['variable'] not in variables or not isinstance(atom['relation'], str) or atom['relation'] not in RELATIONS:
                raise InputError('A comparison needs a declared variable and supported relation.')
            _keys(atom['value'], {'numerator', 'denominator'})
            p, q = atom['value']['numerator'], atom['value']['denominator']
            if type(p) is not int or type(q) is not int or abs(p) > 1000 or not 1 <= q <= 1000 or Fraction(p, q).denominator != q:
                raise InputError('Condition constants must be reduced exact rationals bounded by 1000.')
        else:
            _keys(atom, {'op', 'lhs', 'relation', 'rhs'})
            if atom['op'] != 'expr_compare' or atom['relation'] not in ['eq', 'ne'] or atom['rhs'] != {'op': 'int', 'value': 0}:
                raise InputError('Function conditions compare an expression to zero with = or !=.')
            _validate_expr(atom['lhs'], variables)
            if atom['relation'] == 'eq' and ((atom['lhs'] == data['lhs'] and atom['rhs'] == data['rhs']) or (atom['lhs'] == data['rhs'] and atom['rhs'] == data['lhs'])):
                raise NeedsConditions('The target equality is itself an assumption; choose an independent target.')
        key = json.dumps(atom, sort_keys=True)
        if key in seen:
            raise InputError('Conditions must be distinct.')
        seen.add(key)
    for atom in assumptions:
        if atom['op'] == 'expr_compare' and {**atom, 'relation': 'ne' if atom['relation'] == 'eq' else 'eq'} in assumptions:
            raise NeedsConditions('A function expression cannot be both zero and nonzero.')
    bounds = domains(data)
    validate_order_domains([data['lhs'], data['rhs'], assumptions], bounds)
    if 'proof' in data:
        from .real_special import has_special, validate_proof
        if has_special(data):
            validate_proof(data)
        elif data['proof'] != {'mode': 'diagnostic'}:
            raise InputError('Bessel version 2 targets use proof mode diagnostic.')
    return data


def display(node):
    op = node['op']
    if op == 'int': return str(node['value'])
    if op == 'var': return node['name']
    if op == 'rational': return str(Fraction(node['numerator'], node['denominator']))
    if op == 'neg': return f'(-{display(node["arg"])})'
    if op in {'add', 'sub', 'mul', 'div'}:
        return '(' + display(node['args'][0]) + {'add': '+', 'sub': '-', 'mul': '*', 'div': '/'}[op] + display(node['args'][1]) + ')'
    if op == 'pow': return f'({display(node["base"])}^{node["exponent"]})'
    if op == 'rpow': return f'({display(node["base"])}^({display(node["exponent"])}))'
    if op == 'gamma': return f'Gamma({display(node["arg"])})'
    if op == 'exp': return f'exp({display(node["arg"])})'
    if op == 'erf': return f'erf({display(node["arg"])})'
    if op == 'sqrt': return f'sqrt({display(node["arg"])})'
    if op == 'pi': return 'pi'
    if op == 'deriv': return f'D_{node["var"]}({display(node["arg"])})'
    if op in {'hermite_h', 'hermite_he'}:
        return f'{"H" if op == "hermite_h" else "He"}_{{{display(node["order"])}}}({display(node["arg"])})'
    if op == 'bessel_y_noninteger': return f'YNoninteger({display(node["order"])},{display(node["arg"])})'
    if op == 'legendre': return f'P_{{{display(node["order"])}}}({display(node["arg"])})'
    if op in {'laguerre', 'jacobi'}:
        parameters = [node['alpha']] + ([node['beta']] if op == 'jacobi' else [])
        return ('Laguerre' if op == 'laguerre' else 'Jacobi') + '(' + ','.join(map(display, [node['order'], *parameters, node['arg']])) + ')'
    if op == 'infinity': return 'infinity'
    if op == 'integral': return f'int({display(node["lower"])},{display(node["upper"])},{display(node["body"])},{node["var"]})'
    if op in {'bessel_j', 'bessel_y'}:
        return f'{"J" if op == "bessel_j" else "Y"}_{{{display(node["order"])}}}({display(node["arg"])})'
    if op == 'bessel_cross':
        return f'X_{{{display(node["orders"][0])},{display(node["orders"][1])}}}({display(node["args"][0])},{display(node["args"][1])})'
    raise InputError('Cannot display an unknown real expression.')


def labels(data):
    result = [f'{name} is {kind}' for name, kind in sorted(data['variables'].items())]
    for a in data['assumptions']:
        if a['op'] == 'compare':
            result.append(f'{a["variable"]} {RELATIONS[a["relation"]]} {Fraction(a["value"]["numerator"], a["value"]["denominator"])}')
        else:
            result.append(f'{display(a["lhs"])} {RELATIONS[a["relation"]]} 0')
    return result


def _positive(node, bounds):
    value = _constant(node)
    if value is not None: return value > 0
    if node['op'] == 'pi': return True
    if node['op'] == 'var':
        lo = bounds.get(node['name'], [None, None, set()])[0]
        return lo is not None and (lo[0] > 0 or (lo[0] == 0 and lo[1]))
    if node['op'] == 'exp': return True
    if node['op'] == 'gamma': return _positive(node['arg'], bounds)
    if node['op'] == 'sqrt': return _positive(node['arg'], bounds)
    if node['op'] in {'add', 'mul', 'div'}: return all(_positive(n, bounds) for n in node['args'])
    if node['op'] == 'pow': return node['exponent'] == 0 or _positive(node['base'], bounds)
    return False


def template_match(data):
    """Match the documented root identity without changing the fixed target."""
    from .parser import _Parser
    bounds = domains(data)
    for variable in ['z', 'x']:
        if set(data['variables']) != {'lambda', variable}:
            continue
        lo, hi, _ = bounds['lambda']
        vlo = bounds[variable][0]
        if not (lo and (lo[0] > 0 or lo == (0, True)) and hi and (hi[0] < 1 or hi == (1, True)) and vlo and (vlo[0] > 0 or vlo == (0, True))):
            continue
        A = f'X_00({variable},lambda*{variable})'
        B = f'X_11({variable},lambda*{variable})'
        C = f'X_02({variable},lambda*{variable})'
        Q = f'X_01({variable},{variable})'
        left = f'{A}^2/({Q}^2+lambda^2*{A}*{C})'
        root = _convert(_Parser(f'X_01({variable},lambda*{variable})', extended=True).expression())
        if {'op': 'expr_compare', 'lhs': root, 'relation': 'eq', 'rhs': {'op': 'int', 'value': 0}} not in data['assumptions']:
            continue
        for right in [f'(1/lambda)*{A}/({B}-lambda*{A})', f'(1/lambda)*({A}/({B}-lambda*{A}))']:
            lhs, rhs = map(_convert, _Parser(left+'='+right, extended=True).equation())
            if (data['lhs'], data['rhs']) in [(lhs, rhs), (rhs, lhs)]:
                return {'id': 'cross_product_root_fraction', 'root_variable': variable,
                        'substitutions': {'lam': 'lambda', 'A': A, 'B': B, 'C': C, 'Q': Q},
                        'assumptions': ['0 < lam', 'Q != 0', 'C = -A', 'lam*A*B = Q^2', '0 < Q^2-lam^2*A^2'],
                        'steps': ['次数2の漸化式と根条件より C=-A。', f'交差積の行列式とWronskianより lam*A*B=Q^2、Q=-2/(pi*{variable})。',
                                  f'u(t)=X_00({variable},t) のBessel方程式を積分すると Q^2-lam^2*A^2=(2/{variable}^2)*integral(lam*{variable},{variable},t*u(t)^2) > 0。',
                                  '分母を lam*A*(B-lam*A) に因数分解し、非零性を用いて約分する。'],
                        'sources': ['https://dlmf.nist.gov/10.6.E1', 'https://dlmf.nist.gov/10.6.E10', 'https://dlmf.nist.gov/10.5.E2', 'https://dlmf.nist.gov/10.2.E1'],
                        'formal_obligations': ['Bessel Y and X definitions', 'root recurrence', 'Wronskian scaling', 'positive energy integral']}
    from .bessel_y_integer import match
    return match(data)


def domain_obligations(data, template):
    bounds = domains(data)
    explicit = [a['lhs'] for a in data['assumptions'] if a['op'] == 'expr_compare' and a['relation'] == 'ne']
    pending = []
    derived_denominators = [n['args'][1] for n in _walk([data['lhs'], data['rhs']]) if n.get('op') == 'div'] if template and template['id'] == 'cross_product_root_fraction' else []
    def nonzero(n):
        value = _constant(n)
        if value is not None: return value != 0
        if n in explicit or _positive(n, bounds): return True
        if n['op'] == 'var': return 0 in bounds.get(n['name'], [None, None, set()])[2]
        if n['op'] == 'neg': return nonzero(n['arg'])
        if n['op'] in {'mul', 'div'}: return all(nonzero(a) for a in n['args'])
        if n['op'] == 'pow': return n['exponent'] == 0 or nonzero(n['base'])
        return False
    for node in _walk([data['lhs'], data['rhs'], data['assumptions']]):
        if node.get('op') in {'bessel_j', 'bessel_y', 'bessel_cross', 'bessel_y_noninteger'}:
            for arg in node['args'] if node['op'] == 'bessel_cross' else [node['arg']]:
                if not _positive(arg, bounds):
                    pending.append(display(arg)+' > 0')
        if node.get('op') == 'div' and not nonzero(node['args'][1]) and node['args'][1] not in derived_denominators:
            pending.append(display(node['args'][1])+' != 0')
    # The exact template supplies an analytic proof of its two denominators.
    return sorted(set(pending))


def conditional_source(template=None):
    if template and template['id'] == 'integer_y_recurrence':
        from .bessel_y_integer import conditional_source as integer_y_source
        return integer_y_source(template)
    return TEMPLATE.read_text(encoding='utf-8')


def verify_diagnostic(data, output_dir, timeout):
    from .real_numeric import diagnose
    template = template_match(data)
    pending = domain_obligations(data, template)
    numeric = diagnose(data)
    conditional = {'accepted': False, 'reason': 'no_matching_analytic_template'}
    if template:
        source = conditional_source(template)
        path = output_dir / 'conditional_certificate.lean'
        path.write_text(source, encoding='utf-8')
        conditional = {**_run_lean(path, timeout), 'scope': template.get('scope', 'algebra_under_explicit_bessel_hypotheses'),
                       'assumptions': template['assumptions'], 'sha256': _sha(source.encode())}
    result = {'status': 'needs_conditions' if pending else 'unresolved',
              'reason': 'domain_conditions_required' if pending else 'bessel_y_formalization_pending',
              'statement': display(data['lhs'])+' = '+display(data['rhs']), 'conditions': labels(data),
              'definitions': {'bessel_cross': CROSS_DEFINITION}, 'environment': environment(),
              'full_bessel_proof': False, 'pending_domain_conditions': pending,
              'analysis': template, 'conditional_lean': conditional, 'numerical': numeric,
              'request_sha256': _sha((output_dir/'request.json').read_bytes())}
    _save_json(output_dir/'analysis.json', template or {'status': 'no_matching_template'})
    _save_json(output_dir/'numerical.json', numeric)
    _save_json(output_dir/'result.json', result)
    remaining = ('Jの次数0と1での次数微分可能性の証明が残っています。'
                 if template and template['id'] == 'integer_y_recurrence' else
                 '整数Yと交差積の解析公式への接続が残っています。')
    lines = ['# 正実数のBessel診断', '', result['statement'], '', '条件：'+'、'.join(labels(data)), '',
             '状態：'+result['status']+'。'+remaining, '',
             '数値診断：'+numeric['diagnostic']+'。有限標本の結果を numerical.json に保存しました。']
    if template:
        lines += ['', '## 解析テンプレート', *template['steps'], '', '## 条件付きLean',
                  '明示前提の下での検査：'+str(conditional['accepted'])+'。仮定：'+'、'.join(template['assumptions']),
                  '残る形式化：'+'、'.join(template['formal_obligations'])]
    if pending:
        lines += ['', '確認する定義域条件：'+'、'.join(pending)]
    (output_dir/'report.md').write_text('\n'.join(lines)+'\n', encoding='utf-8')
    return result


def replay_diagnostic(data, result, output_dir, timeout):
    if result.get('status') not in {'unresolved', 'needs_conditions'} or result.get('full_bessel_proof') is not False:
        raise InputError('A version 2 diagnostic cannot carry proved/refuted status.')
    if result.get('request_sha256') != _sha((output_dir/'request.json').read_bytes()) or result.get('environment') != environment():
        raise InputError('The saved target or mathematical environment changed.')
    template = template_match(data)
    if not template or result.get('analysis') != template:
        raise InputError('This target has no matching conditional certificate.')
    if load_json(output_dir/'analysis.json') != template:
        raise InputError('The saved conditional analysis changed.')
    source = conditional_source(template)
    path = output_dir/'conditional_certificate.lean'
    if path.read_text(encoding='utf-8') != source or result.get('conditional_lean', {}).get('sha256') != _sha(source.encode()):
        raise InputError('The conditional certificate differs from the fixed template.')
    conditional = result.get('conditional_lean', {})
    if (conditional.get('scope') != template.get('scope', 'algebra_under_explicit_bessel_hypotheses') or
            conditional.get('assumptions') != template['assumptions']):
        raise InputError('The saved conditional scope or assumptions changed.')
    checked = _run_lean(path, timeout)
    return {'status': result['status'], 'replayed': False, 'conditional_replayed': checked['accepted'],
            'full_bessel_proof': False, 'verification': checked}
