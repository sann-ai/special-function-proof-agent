"""Closed additional analytic grammars with preserved original domain obligations."""
from copy import deepcopy
from fractions import Fraction

from .core import InputError, _keys
from .real_bessel import is_variable_name
from . import research_user_analytic as previous

OPS = {'geometric_series_definition', 'elementary_integral_definition',
       'nonlinear_ode_definition', 'second_order_ode_definition'}
MAX_TERMS = 16
MAX_DEGREE = 12
MAX_RATIONAL_LITERAL = 1000
MAX_RATIONAL_BITS = 64
_FIELDS = {
    'geometric_series_definition': {'op', 'index', 'term'},
    'elementary_integral_definition': {'op', 'var', 'integrand', 'lower', 'upper'},
    'nonlinear_ode_definition': {'op', 'var', 'state', 'rhs', 'initial_time', 'initial_value', 'arg'},
    'second_order_ode_definition': {'op', 'var', 'state', 'velocity', 'rhs',
                                    'initial_time', 'initial_value', 'initial_derivative', 'arg'},
}


def _fraction(node):
    """Evaluate the bounded exact constant grammar, without symbolic inference."""
    op = previous._operation(node)
    if op == 'int':
        value = Fraction(node['value'])
    elif op == 'neg':
        child = _fraction(node['arg'])
        if child is None: return None
        value = -child
    elif op in {'add', 'sub', 'mul', 'div'}:
        left, right = (_fraction(child) for child in node['args'])
        if left is None or right is None: return None
        if op == 'div' and right == 0:
            raise InputError('A fixed rational base or slope requires a nonzero denominator.')
        if op == 'add': value = left + right
        elif op == 'sub': value = left - right
        elif op == 'mul': value = left * right
        else: value = left / right
    else:
        return None
    if max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > MAX_RATIONAL_BITS:
        raise InputError('Fixed rational arithmetic exceeds the 64-bit intermediate size limit.')
    return value


def _rational_value(value):
    if max(abs(value.numerator), value.denominator) > MAX_RATIONAL_LITERAL:
        raise InputError('A normalized rational numerator and denominator must each be at most 1000.')
    return {'numerator': value.numerator, 'denominator': value.denominator}


def _rational_expr(value):
    parts = _rational_value(value)
    if parts['denominator'] == 1: return previous._int(parts['numerator'])
    return {'op': 'div', 'args': [previous._int(parts['numerator']), previous._int(parts['denominator'])]}


def _sign(node):
    sign = 1
    while node.get('op') == 'neg':
        sign, node = -sign, node['arg']
    return sign, node


def _bounded_base(node):
    sign, unsigned = _sign(node)
    if unsigned['op'] != 'div': return None
    numerator, denominator = unsigned['args']
    if denominator['op'] != 'add': return None
    for one, square in (denominator['args'], list(reversed(denominator['args']))):
        if _fraction(one) != 1: continue
        if square['op'] == 'pow' and square['exponent'] == 2:
            argument = square['base']
        elif square['op'] == 'mul' and square['args'][0] == square['args'][1]:
            argument = square['args'][0]
        else:
            continue
        numerator_sign, numerator_core = _sign(numerator)
        _, argument_core = _sign(argument)
        if numerator_core == argument_core:
            return {'base_kind': 'bounded_rational', 'base_argument': argument_core,
                    'base_sign': sign * numerator_sign}
    return None


def _kernel_present(node):
    if isinstance(node, dict):
        return (isinstance(node.get('op'), str) and node['op'] in {'exp', 'sin', 'cos'}
                or any(_kernel_present(value) for value in node.values()))
    return isinstance(node, list) and any(_kernel_present(value) for value in node)


class _Normalizer(previous._Normalizer):
    def __init__(self, parameters):
        super().__init__(parameters)
        self.conditions = {}
        self.affine_arguments = {}

    def count_kernel(self):
        self.kernel_count += 1
        if self.kernel_count > MAX_TERMS:
            raise InputError('An advanced analytic definition supports at most 16 kernel occurrences, including cancelled terms.')

    def geometric_kernel(self, node, index):
        if node['op'] != 'pow': return None
        _keys(node, {'op', 'base', 'exponent'})
        if node['exponent'] != {'op': 'var', 'name': index}:
            return None
        argument = self.scalar(node['base'])
        value = _fraction(argument)
        if value is not None:
            if not abs(value) < 1:
                raise InputError('A geometric base requires absolute value strictly below one.')
            info = {'base_kind': 'rational', 'base_value': _rational_value(value)}
        else:
            info = _bounded_base(argument)
            if info is None:
                raise InputError('Geometric bases use a fixed rational with |q|<1 or ±u/(1+u²); a free base q needs a separate convergence premise.')
        self.count_kernel()
        condition = {'kind': 'abs_lt_one', 'argument': argument}
        self.conditions.setdefault(previous._canonical(condition), condition)
        return {'coefficient': previous._int(1), 'argument': argument, **info}

    def elementary_kernel(self, node, var):
        if node['op'] not in {'exp', 'sin', 'cos'}: return None
        _keys(node, {'op', 'arg'})
        polynomial = self.trim(self.polynomial(node['arg'], var))
        if any(degree[0] > 1 for degree in polynomial):
            raise InputError('An elementary integral kernel requires an affine argument in its bound variable.')
        slope = _fraction(polynomial.get((1, 0), previous._int(0)))
        if slope is None:
            raise InputError('An elementary integral slope must normalize to a fixed rational; its intercept may depend on real parameters.')
        slope = _rational_expr(slope)
        intercept = polynomial.get((0, 0), previous._int(0))
        self.count_kernel()
        affine = {'original': node['arg'], 'slope': slope, 'intercept': intercept}
        self.affine_arguments.setdefault(previous._canonical(affine), affine)
        return {'kind': node['op'], 'coefficient': previous._int(1), 'slope': slope, 'intercept': intercept}

    def combination(self, node, binder, geometric=False):
        op = previous._operation(node)
        term = self.geometric_kernel(node, binder) if geometric else self.elementary_kernel(node, binder)
        if term is not None: return [term]
        recurse = lambda child: self.combination(child, binder, geometric)
        if op in {'add', 'sub'}:
            left, right = previous._binary(node)
            first, second = recurse(left), recurse(right)
            if op == 'sub': second = [{**item, 'coefficient': previous._neg(item['coefficient'])} for item in second]
            return first + second
        if op == 'neg':
            _keys(node, {'op', 'arg'})
            return [{**item, 'coefficient': previous._neg(item['coefficient'])} for item in recurse(node['arg'])]
        if op == 'mul':
            left, right = previous._binary(node)
            left_bound = previous._mentions(left, {binder})
            right_bound = previous._mentions(right, {binder})
            if left_bound and right_bound:
                raise InputError('Kernel multiplication needs a coefficient independent of the bound variable.')
            if left_bound: factor, body = right, left
            elif right_bound: factor, body = left, right
            elif not geometric and _kernel_present(right): factor, body = left, right
            elif not geometric and _kernel_present(left): factor, body = right, left
            else:
                self.scalar(node)
                if previous._literal(previous._coefficient(node), 0): return []
                raise InputError('A nonzero combination term must contain one supported analytic kernel.')
            factor = self.scalar(factor)
            return [{**item, 'coefficient': previous._mul(factor, item['coefficient'])} for item in recurse(body)]
        if op == 'div':
            numerator, denominator = previous._binary(node)
            if previous._mentions(denominator, {binder}):
                raise InputError('A kernel coefficient denominator must be independent of the bound variable.')
            divisor = self.scalar(denominator)
            self.denominators.setdefault(previous._canonical(divisor), divisor)
            return [{**item, 'coefficient': previous._div(item['coefficient'], divisor)} for item in recurse(numerator)]
        if not previous._mentions(node, {binder}):
            self.scalar(node)
            if previous._literal(node, 0): return []
        raise InputError('Use a finite linear combination of the operation’s supported kernels.')

    def nonlinear(self, node, var, state):
        used = {name.casefold() for name in self.parameters} | {var.casefold(), state.casefold()}
        def names(value):
            if isinstance(value, dict):
                if value.get('op') == 'var' and isinstance(value.get('name'), str): used.add(value['name'].casefold())
                for child in value.values(): names(child)
            elif isinstance(value, list):
                for child in value: names(child)
        names(node)
        index = 0
        while 'analytickernel'+str(index) in used: index += 1
        fresh = 'analyticKernel'+str(index)
        state_node = {'op': 'var', 'name': state}
        squares = [{'op': 'pow', 'base': state_node, 'exponent': 2},
                   {'op': 'mul', 'args': [state_node, state_node]}]
        radicands = [{'op': 'add', 'args': items} for square in squares
                     for items in ([previous._int(1), square], [square, previous._int(1)])]
        def replace(value):
            if isinstance(value, dict):
                if value.get('op') == 'sqrt' and previous._mentions(value, {state}):
                    _keys(value, {'op', 'arg'})
                    if value['arg'] not in radicands:
                        raise InputError('The nonlinear state kernel must be sqrt(1+y²), with this definition’s state variable.')
                    self.count_kernel()
                    self.scalar(previous._int(1))
                    return {'op': 'var', 'name': fresh}
                if value.get('op') == 'var' and value.get('name') == state:
                    raise InputError('The nonlinear state occurs only inside sqrt(1+y²).')
                return {key: replace(child) for key, child in value.items()}
            if isinstance(value, list): return [replace(child) for child in value]
            return value
        polynomial = self.trim(self.polynomial(replace(node), var, fresh))
        if any(degree[1] != 1 for degree in polynomial):
            raise InputError('The nonlinear right side must be p(t)*sqrt(1+y²), with zero independent term and one kernel factor.')
        return polynomial


def normalize(node, parameters):
    """Return deterministic typed normal forms and all original scalar obligations."""
    previous._bounded(node)
    op = previous._operation(node)
    if op not in OPS:
        raise InputError('Choose one of the four advanced analytic definition operations.')
    _keys(node, _FIELDS[op])
    if (not isinstance(parameters, dict) or len(parameters) > 3
            or any(not is_variable_name(name) or kind != 'real' for name, kind in parameters.items())
            or len({name.casefold() for name in parameters}) != len(parameters)):
        raise InputError('Advanced analytic normalization accepts zero to three distinct real parameters.')
    binder_fields = ('index',) if op == 'geometric_series_definition' else (
        ('var',) if op == 'elementary_integral_definition' else
        ('var', 'state') if op == 'nonlinear_ode_definition' else ('var', 'state', 'velocity'))
    binders = [node[field] for field in binder_fields]
    if (any(not is_variable_name(name) for name in binders)
            or len({name.casefold() for name in binders}) != len(binders)
            or {name.casefold() for name in binders} & {name.casefold() for name in parameters}):
        raise InputError('Time, index, state and velocity binders must be distinct safe ASCII names separate from real parameters.')
    context = _Normalizer(parameters)
    result = {'op': op, **{field: node[field] for field in binder_fields}}
    if op == 'geometric_series_definition':
        result['terms'] = context.combination(node['term'], node['index'], geometric=True)
        value_fields = ()
    elif op == 'elementary_integral_definition':
        result['terms'] = context.combination(node['integrand'], node['var'])
        result['affine_arguments'] = [context.affine_arguments[key] for key in sorted(context.affine_arguments)]
        value_fields = ('lower', 'upper')
    else:
        if op == 'nonlinear_ode_definition':
            polynomial = context.nonlinear(node['rhs'], node['var'], node['state'])
            kernel_power = 1
            value_fields = ('initial_time', 'initial_value', 'arg')
        else:
            if previous._mentions(node['rhs'], {node['state'], node['velocity']}):
                raise InputError('Second-order polynomial forcing depends on time and real parameters; state and velocity occurrences are excluded before cancellation.')
            polynomial = context.trim(context.polynomial(node['rhs'], node['var']))
            kernel_power = 0
            value_fields = ('initial_time', 'initial_value', 'initial_derivative', 'arg')
        degree = max((key[0] for key in polynomial), default=0)
        result['coefficients'] = [polynomial.get((power, kernel_power), previous._int(0)) for power in range(degree + 1)]
    for field in value_fields: result[field] = context.scalar(node[field])
    result['scalar_expressions'] = [context.scalars[key] for key in sorted(context.scalars)]
    result['nonzero_denominators'] = [context.denominators[key] for key in sorted(context.denominators)]
    result['required_conditions'] = [context.conditions[key] for key in sorted(context.conditions)]
    previous._bounded(result)
    result = {key: deepcopy(value) for key, value in result.items()}
    result['original'] = deepcopy(node)
    return result
