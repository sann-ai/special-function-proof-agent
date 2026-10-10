"""Closed real analytic definitions and their proved finite-expression bridges."""
from copy import deepcopy

from .core import InputError, _keys

OPS = {'exp_series', 'gaussian_primitive', 'linear_ivp'}
_FIELDS = {'exp_series': ('arg',), 'gaussian_primitive': ('arg',),
           'linear_ivp': ('rate', 'initial', 'arg')}
_NAMESPACE = 'SpecialFunctionProofAgent.'
_DEFINITIONS = {'exp_series': 'exponentialSeries', 'gaussian_primitive': 'gaussianPrimitive',
                'linear_ivp': 'homogeneousIVPSolution'}
_BRIDGES = {'exp_series': 'exponentialSeries_eq_exp', 'gaussian_primitive': 'gaussianPrimitive_eq_erf',
            'linear_ivp': 'homogeneousIVPSolution_eq_exp'}


def fields(node):
    """Check the closed primitive shape; the caller type-checks finite children."""
    if not isinstance(node, dict) or not isinstance(node.get('op'), str) or node['op'] not in OPS:
        raise InputError('Choose exp_series, gaussian_primitive, or linear_ivp.')
    result = _FIELDS[node['op']]
    _keys(node, {'op', *result})
    for field in result:
        if not isinstance(node[field], dict):
            raise InputError('Analytic definition arguments must be finite real expression objects.')
    pending = [(node[field], 0) for field in result]
    count = 0
    while pending:
        value, depth = pending.pop()
        count += 1
        if depth > 24 or count > 1200:
            raise InputError('Analytic arguments exceed the finite expression size or depth limit.')
        if isinstance(value, dict):
            if value.get('op') in (*OPS, 'deriv', 'integral', 'infinity', 'defined'):
                raise InputError('Analytic arguments use existing finite expressions without analytic or defined calls, derivatives, or integrals.')
            pending.extend((child, depth+1) for child in value.values())
        elif isinstance(value, list):
            pending.extend((child, depth+1) for child in value)
    return result


def expand(node):
    """Return the finite expression proved equal to this original analytic call."""
    fields(node)
    arg = deepcopy(node['arg'])
    if node['op'] == 'exp_series':
        return {'op': 'exp', 'arg': arg}
    if node['op'] == 'gaussian_primitive':
        factor = {'op': 'div', 'args': [{'op': 'sqrt', 'arg': {'op': 'pi'}}, {'op': 'int', 'value': 2}]}
        return {'op': 'mul', 'args': [factor, {'op': 'erf', 'arg': arg}]}
    exponent = {'op': 'mul', 'args': [deepcopy(node['rate']), arg]}
    return {'op': 'mul', 'args': [deepcopy(node['initial']), {'op': 'exp', 'arg': exponent}]}


def lean_expr(node, renderChild):
    """Render the analytic definition itself with rate/initial/evaluation in order."""
    arguments = ' '.join('('+renderChild(node[field])+')' for field in fields(node))
    return '('+_NAMESPACE+_DEFINITIONS[node['op']]+' '+arguments+')'


def contracts(node):
    """Describe the fixed analytic object and its all-real bridge deterministically."""
    arguments = {field: deepcopy(node[field]) for field in fields(node)}
    op = node['op']
    if op == 'exp_series':
        kind = 'convergent_power_series'
        semantics = {'index_domain': 'nat', 'first_index': 0, 'term': 'arg^n / n!',
                     'summation': 'infinite'}
        theorems = ['hasSum_exponentialSeries', 'summable_exponentialSeries']
    elif op == 'gaussian_primitive':
        kind = 'oriented_finite_integral'
        semantics = {'lower_endpoint': 0, 'upper_endpoint': 'arg', 'integrand': 'exp(-(t^2))',
                     'orientation': 'from_zero_to_arg', 'measure': 'real_volume'}
        theorems = ['intervalIntegrable_gaussian', 'hasDerivAt_gaussianPrimitive']
    else:
        kind = 'unique_global_ivp_solution'
        semantics = {'time_domain': 'real', 'equation': "y'(t) = rate*y(t)",
                     'fixed_parameters': ['rate', 'initial'],
                     'initial_condition': {'time': 0, 'value': 'initial'},
                     'evaluation_argument': 'arg',
                     'solution_class': 'real functions differentiable at every real time'}
        theorems = ['hasDerivAt_homogeneousIVPSolution', 'homogeneousIVPSolution_zero',
                    'homogeneousIVPSolution_unique', 'existsUnique_homogeneousIVPSolution']
    return {'op': op, 'kind': kind, 'domain': {field: 'real' for field in arguments},
            'arguments': arguments, 'semantics': semantics,
            'definition': _NAMESPACE+_DEFINITIONS[op], 'bridge': _NAMESPACE+_BRIDGES[op],
            'theorems': [_NAMESPACE+name for name in theorems]}


def rewrite_lemmas():
    """Use only the three fixed bridges from analytic objects to closed forms."""
    return [_NAMESPACE+_BRIDGES[op] for op in ('exp_series', 'gaussian_primitive', 'linear_ivp')]
