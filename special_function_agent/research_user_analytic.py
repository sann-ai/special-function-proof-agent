"""Bounded user series, polynomial integrals, and scalar homogeneous ODE syntax."""
from copy import deepcopy
import json

from .core import InputError, _keys
from .real_bessel import is_variable_name

OPS = {'series_definition', 'integral_definition', 'ode_definition'}
MAX_TERMS = 16
MAX_DEGREE = 12
MAX_DEPTH = 24
MAX_NODES = 1200
MAX_BYTES = 256 * 1024
_FIELDS = {
    'series_definition': {'op', 'index', 'term'},
    'integral_definition': {'op', 'var', 'integrand', 'lower', 'upper'},
    'ode_definition': {'op', 'var', 'state', 'rhs', 'initial_time', 'initial_value', 'arg'},
}


def _bounded(value):
    pending = [(value, 0)]
    count = 0
    while pending:
        item, depth = pending.pop()
        if depth > MAX_DEPTH:
            raise InputError('User analytic syntax exceeds the depth limit of 24.')
        if isinstance(item, dict):
            count += 1
            if any(not isinstance(key, str) for key in item):
                raise InputError('User analytic objects require string keys.')
            pending.extend((child, depth + 1) for child in item.values())
        elif isinstance(item, list):
            count += 1
            if len(item) > MAX_NODES:
                raise InputError('User analytic syntax exceeds the size limit of 1200 nodes.')
            pending.extend((child, depth) for child in item)
        elif not (isinstance(item, str) or type(item) is int):
            raise InputError('User analytic syntax requires finite typed JSON expressions.')
        if count > MAX_NODES:
            raise InputError('User analytic syntax exceeds the size limit of 1200 nodes.')
    try:
        size = len(_canonical(value).encode('utf-8'))
    except UnicodeError as exc:
        raise InputError('User analytic syntax requires UTF-8 text.') from exc
    if size > MAX_BYTES:
        raise InputError('User analytic syntax exceeds the 256 KiB limit.')


def _canonical(value):
    try:
        return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False, allow_nan=False)
    except (TypeError, ValueError, UnicodeError, RecursionError) as exc:
        raise InputError('User analytic syntax requires bounded UTF-8 JSON.') from exc


def _int(value):
    return {'op': 'int', 'value': value}


def _literal(node, value):
    return node == _int(value)


def _neg(node):
    if node['op'] == 'int': return _int(-node['value'])
    if node['op'] == 'neg': return node['arg']
    return {'op': 'neg', 'arg': node}


def _add(left, right):
    if _literal(left, 0): return right
    if _literal(right, 0): return left
    if left == _neg(right): return _int(0)
    if left['op'] == right['op'] == 'int' and abs(left['value'] + right['value']) <= 1000:
        return _int(left['value'] + right['value'])
    return {'op': 'add', 'args': [left, right]}


def _mul(left, right):
    if _literal(left, 0) or _literal(right, 0): return _int(0)
    if _literal(left, 1): return right
    if _literal(right, 1): return left
    if _literal(left, -1): return _neg(right)
    if _literal(right, -1): return _neg(left)
    if left['op'] == right['op'] == 'int' and abs(left['value'] * right['value']) <= 1000:
        return _int(left['value'] * right['value'])
    return {'op': 'mul', 'args': [left, right]}


def _div(left, right):
    if _literal(left, 0): return _int(0)
    if _literal(right, 1): return left
    return {'op': 'div', 'args': [left, right]}


def _coefficient(node):
    op = node['op']
    if op == 'neg': return _neg(_coefficient(node['arg']))
    if op in {'add', 'sub', 'mul', 'div'}:
        left, right = (_coefficient(child) for child in node['args'])
        if op == 'sub': return _add(left, _neg(right))
        return {'add': _add, 'mul': _mul, 'div': _div}[op](left, right)
    return node


def _mentions(node, names):
    if isinstance(node, dict):
        return ((node.get('op') == 'var' and isinstance(node.get('name'), str) and node['name'] in names)
                or any(_mentions(child, names) for child in node.values()))
    return isinstance(node, list) and any(_mentions(child, names) for child in node)


def _binary(node):
    _keys(node, {'op', 'args'})
    if not isinstance(node['args'], list) or len(node['args']) != 2:
        raise InputError('A user analytic binary operation requires two arguments.')
    return node['args']


def _operation(node):
    if not isinstance(node, dict) or not isinstance(node.get('op'), str):
        raise InputError('Every user analytic expression requires an operation string.')
    return node['op']


class _Normalizer:
    def __init__(self, parameters):
        self.parameters = parameters
        self.scalars = {}
        self.denominators = {}
        self.kernel_count = 0

    def scalar(self, node):
        # Imported at call time because research_functions delegates syntax here.
        from .research_functions import _finite
        _finite(node, self.parameters)
        self.scalars.setdefault(_canonical(node), node)
        return node

    def series(self, node, index):
        op = _operation(node)
        if not _mentions(node, {index}):
            self.scalar(node)
            if _literal(node, 0): return []
            raise InputError('Series terms must be finite linear combinations of q^k/k! kernels; only zero is an index-independent summand.')
        if op == 'div':
            numerator, denominator = _binary(node)
            if (isinstance(numerator, dict) and numerator.get('op') == 'pow'
                    and numerator.get('exponent') == {'op': 'var', 'name': index}):
                _keys(numerator, {'op', 'base', 'exponent'})
                expected = {'op': 'factorial', 'arg': {'op': 'var', 'name': index}}
                if denominator != expected:
                    raise InputError('A series kernel denominator must be factorial of the same bound natural index.')
                argument = self.scalar(numerator['base'])
                self.kernel_count += 1
                if self.kernel_count > MAX_TERMS:
                    raise InputError('A series definition supports at most 16 kernel terms.')
                return [{'coefficient': _int(1), 'argument': argument}]
            if _mentions(denominator, {index}):
                raise InputError('Series coefficients may divide only by index-independent finite real expressions; kernels use exactly k!.')
            divisor = self.scalar(denominator)
            self.denominators.setdefault(_canonical(divisor), divisor)
            return [{'coefficient': _div(term['coefficient'], divisor), 'argument': term['argument']}
                    for term in self.series(numerator, index)]
        if op in {'add', 'sub'}:
            left, right = _binary(node)
            first, second = self.series(left, index), self.series(right, index)
            if op == 'sub':
                second = [{'coefficient': _neg(term['coefficient']), 'argument': term['argument']} for term in second]
            return first + second
        if op == 'neg':
            _keys(node, {'op', 'arg'})
            return [{'coefficient': _neg(term['coefficient']), 'argument': term['argument']}
                    for term in self.series(node['arg'], index)]
        if op == 'mul':
            left, right = _binary(node)
            left_bound, right_bound = _mentions(left, {index}), _mentions(right, {index})
            if left_bound and right_bound:
                raise InputError('Series multiplication requires one index-independent finite coefficient.')
            factor, body = (right, left) if left_bound else (left, right)
            coefficient = self.scalar(factor)
            return [{'coefficient': _mul(coefficient, term['coefficient']), 'argument': term['argument']}
                    for term in self.series(body, index)]
        raise InputError('Supported series kernels have the exact form pow(q, k) / factorial(k), combined linearly.')

    def polynomial(self, node, var, state=None):
        op = _operation(node)
        bound = {var} if state is None else {var, state}
        if not _mentions(node, bound):
            return {(0, 0): _coefficient(self.scalar(node))}
        if op == 'var':
            _keys(node, {'op', 'name'})
            return {(1, 0) if node['name'] == var else (0, 1): _int(1)}
        if op == 'neg':
            _keys(node, {'op', 'arg'})
            return {key: _neg(value) for key, value in self.polynomial(node['arg'], var, state).items()}
        if op in {'add', 'sub', 'mul', 'div'}:
            left, right = _binary(node)
            first = self.polynomial(left, var, state)
            if op == 'div':
                if _mentions(right, bound):
                    raise InputError('Polynomial division requires a finite coefficient independent of time and state.')
                divisor = self.scalar(right)
                self.denominators.setdefault(_canonical(divisor), divisor)
                return {key: _div(value, divisor) for key, value in first.items()}
            second = self.polynomial(right, var, state)
            if op == 'mul': return self.product(first, second)
            result = dict(first)
            for key, value in second.items():
                result[key] = _add(result.get(key, _int(0)), _neg(value) if op == 'sub' else value)
            return self.trim(result)
        if op == 'pow':
            _keys(node, {'op', 'base', 'exponent'})
            exponent = node['exponent']
            if type(exponent) is not int or not 0 <= exponent <= MAX_DEGREE:
                raise InputError('Polynomial natural powers range from zero to twelve.')
            base = self.polynomial(node['base'], var, state)
            result = {(0, 0): _int(1)}
            for _ in range(exponent): result = self.product(result, base)
            return result
        raise InputError('The bound integrand or ODE right side must be a polynomial built from addition, subtraction, multiplication, natural powers, and independent coefficients.')

    @staticmethod
    def trim(polynomial):
        return {key: value for key, value in polynomial.items() if not _literal(value, 0)}

    def product(self, left, right):
        result = {}
        for (i, j), first in left.items():
            for (k, m), second in right.items():
                coefficient = _mul(first, second)
                if _literal(coefficient, 0): continue
                key = (i + k, j + m)
                if max(key) > MAX_DEGREE:
                    raise InputError('Polynomial expansion exceeds degree twelve in a bound variable.')
                result[key] = _add(result.get(key, _int(0)), coefficient)
        result = self.trim(result)
        _bounded(list(result.values()))
        return result


def normalize(node, parameters):
    """Preserve original syntax and normalize a bounded analytic definition.

    ``coefficients`` are ascending real coefficients; ``terms`` preserve series
    kernel order. ``scalar_expressions`` are canonical-JSON-sorted independent
    original subexpressions, retained even when polynomial coefficients cancel.
    """
    _bounded(node)
    op = _operation(node)
    if op not in OPS:
        raise InputError('Choose series_definition, integral_definition, or ode_definition.')
    _keys(node, _FIELDS[op])
    if (not isinstance(parameters, dict) or not 0 <= len(parameters) <= 3
            or any(not is_variable_name(name) or kind != 'real' for name, kind in parameters.items())
            or len({name.casefold() for name in parameters}) != len(parameters)):
        raise InputError('User analytic normalization accepts zero to three distinct real parameters.')
    binders = [node['index']] if op == 'series_definition' else [node['var']]
    if op == 'ode_definition': binders.append(node['state'])
    if (any(not is_variable_name(name) for name in binders)
            or len({name.casefold() for name in binders}) != len(binders)
            or {name.casefold() for name in binders} & {name.casefold() for name in parameters}):
        raise InputError('Analytic binders must be distinct safe ASCII names separate from all real parameters.')
    context = _Normalizer(parameters)
    if op == 'series_definition':
        result = {'op': op, 'index': node['index'], 'terms': context.series(node['term'], node['index'])}
    else:
        state = node.get('state')
        polynomial = context.trim(context.polynomial(node['rhs'] if state else node['integrand'], node['var'], state))
        power = 1 if state else 0
        if state and any(degree[1] != 1 for degree in polynomial):
            raise InputError('An ODE right side must normalize to p(t)*y, with state degree one and zero constant term.')
        degree = max((item[0] for item in polynomial), default=0)
        coefficients = [polynomial.get((index, power), _int(0)) for index in range(degree + 1)]
        result = {'op': op, 'var': node['var'], 'coefficients': coefficients}
        if state:
            result['state'] = state
            fields = ('initial_time', 'initial_value', 'arg')
        else:
            fields = ('lower', 'upper')
        for field in fields: result[field] = context.scalar(node[field])
    result['scalar_expressions'] = [context.scalars[key] for key in sorted(context.scalars)]
    result['nonzero_denominators'] = [context.denominators[key] for key in sorted(context.denominators)]
    _bounded(result)
    result = {key: deepcopy(value) for key, value in result.items()}
    result['original'] = deepcopy(node)
    return result
