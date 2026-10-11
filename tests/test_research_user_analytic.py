"""Pure syntax normalization preserves the chosen series, interval, and IVP."""
from copy import deepcopy
from fractions import Fraction
import json
import math
import unittest

from special_function_agent import research_user_analytic as analytic
from special_function_agent.core import InputError


def integer(value): return {'op': 'int', 'value': value}
def var(name): return {'op': 'var', 'name': name}
def binary(op, left, right): return {'op': op, 'args': [left, right]}
def add(left, right): return binary('add', left, right)
def sub(left, right): return binary('sub', left, right)
def mul(left, right): return binary('mul', left, right)
def div(left, right): return binary('div', left, right)
def neg(arg): return {'op': 'neg', 'arg': arg}
def power(base, exponent): return {'op': 'pow', 'base': base, 'exponent': exponent}
def kernel(argument, index='k'):
    return div(power(argument, var(index)), {'op': 'factorial', 'arg': var(index)})
def series(term, index='k'):
    return {'op': 'series_definition', 'index': index, 'term': term}
def integral(integrand, lower=None, upper=None, binder='t'):
    return {'op': 'integral_definition', 'var': binder, 'integrand': integrand,
            'lower': integer(-2) if lower is None else lower, 'upper': var('x') if upper is None else upper}
def ode(rhs, **kwargs):
    return {'op': 'ode_definition', 'var': 't', 'state': 'y', 'rhs': rhs,
            'initial_time': integer(-1), 'initial_value': var('c'), 'arg': var('x'), **kwargs}


def evaluate(node, values):
    op = node['op']
    if op == 'int': return Fraction(node['value'])
    if op == 'var': return values[node['name']]
    if op == 'neg': return -evaluate(node['arg'], values)
    if op == 'pow':
        exponent = node['exponent']
        return evaluate(node['base'], values) ** (evaluate(exponent, values) if isinstance(exponent, dict) else exponent)
    if op == 'factorial': return math.factorial(int(evaluate(node['arg'], values)))
    left, right = (evaluate(child, values) for child in node['args'])
    return {'add': lambda: left + right, 'sub': lambda: left - right,
            'mul': lambda: left * right, 'div': lambda: left / right}[op]()


class UserAnalyticTests(unittest.TestCase):
    def test_series_multiple_user_terms_and_coefficient_placement(self):
        q, c = var('q'), var('c')
        examples = [kernel(q), add(mul(c, kernel(q)), div(neg(kernel(neg(q))), integer(2))),
                    mul(add(kernel(integer(2)), sub(kernel(q), kernel(integer(-1)))), c)]
        for node in map(series, examples):
            with self.subTest(term=node['term']):
                result = analytic.normalize(node, {'q': 'real', 'c': 'real'})
                for k in range(6):
                    values = {'q': Fraction(-2), 'c': Fraction(3), 'k': k}
                    expected = evaluate(node['term'], values)
                    actual = sum(evaluate(term['coefficient'], values) * evaluate(term['argument'], values)**k / math.factorial(k)
                                 for term in result['terms'])
                    self.assertEqual(actual, expected)
                self.assertEqual(result['original'], node)
        self.assertEqual(analytic.normalize(series(integer(0)), {'x': 'real'})['terms'], [])

    def test_series_has_fixed_natural_index_and_exact_factorial(self):
        bad = [integer(1), var('k'), power(var('q'), var('k')),
               div(power(var('q'), var('k')), var('k')),
               div(power(var('q'), var('k')), {'op': 'factorial', 'arg': add(var('k'), integer(1))}),
               div(power(var('q'), var('k')), {'op': 'factorial', 'arg': var('j')}),
               mul(kernel(var('q')), kernel(var('q'))),
               div(kernel(var('q')), var('k')), kernel(var('k'))]
        for term in bad:
            with self.subTest(term=term), self.assertRaises(InputError):
                analytic.normalize(series(term), {'q': 'real'})

    def test_series_term_count_includes_cancelled_or_zero_scaled_terms(self):
        term = kernel(var('q'))
        for _ in range(15): term = add(term, kernel(var('q')))
        result = analytic.normalize(series(term), {'q': 'real'})
        self.assertEqual(len(result['terms']), 16)
        for too_many in (add(term, kernel(var('q'))), mul(integer(0), add(term, kernel(var('q'))))):
            with self.assertRaisesRegex(InputError, '16'):
                analytic.normalize(series(too_many), {'q': 'real'})

    def test_polynomial_integrals_have_ascending_coefficients_and_oriented_endpoints(self):
        t, q = var('t'), var('q')
        examples = [add(power(t, 3), mul(integer(2), t)), power(add(t, q), 3),
                    div(sub(mul(add(t, q), sub(t, q)), integer(4)), q)]
        for body in examples:
            node = integral(body, var('x'), integer(-3))
            result = analytic.normalize(node, {'q': 'real', 'x': 'real'})
            self.assertEqual((result['lower'], result['upper']), (var('x'), integer(-3)))
            for t_value in (-3, 0, 2):
                values = {'t': Fraction(t_value), 'q': Fraction(2), 'x': Fraction(7)}
                actual = sum(evaluate(coefficient, values) * values['t']**degree
                             for degree, coefficient in enumerate(result['coefficients']))
                self.assertEqual(actual, evaluate(body, values))
        result = analytic.normalize(integral(add(power(t, 3), mul(integer(2), t))), {'x': 'real'})
        self.assertEqual(result['coefficients'], [integer(0), integer(2), integer(0), integer(1)])

    def test_polynomial_zero_and_degree_bound_apply_to_expanded_degree(self):
        t = var('t')
        result = analytic.normalize(integral(sub(t, t)), {'x': 'real'})
        self.assertEqual(result['coefficients'], [integer(0)])
        result = analytic.normalize(integral(power(t, 12)), {'x': 'real'})
        self.assertEqual(len(result['coefficients']), 13)
        for body in (power(t, 13), mul(power(t, 7), power(t, 6)), power(t, -1), power(t, True), power(t, integer(2))):
            with self.subTest(body=body), self.assertRaises(InputError):
                analytic.normalize(integral(body), {'x': 'real'})

    def test_integrands_require_finite_polynomials_in_the_declared_binder(self):
        bad = [{'op': 'exp', 'arg': var('t')}, div(integer(1), var('t')),
               {'op': 'rpow', 'base': var('t'), 'exponent': integer(2)}, var('u')]
        for body in bad:
            with self.subTest(body=body), self.assertRaises(InputError):
                analytic.normalize(integral(body), {'x': 'real'})
        node = integral(mul({'op': 'gamma', 'arg': var('q')}, power(var('t'), 2)))
        result = analytic.normalize(node, {'q': 'real', 'x': 'real'})
        self.assertEqual(result['coefficients'][2], {'op': 'gamma', 'arg': var('q')})

    def test_ode_equivalent_expanded_rhs_and_arbitrary_initial_time(self):
        t, y, q = var('t'), var('y'), var('q')
        examples = [mul(add(power(t, 2), q), y),
                    sub(add(mul(add(t, q), y), mul(y, t)), mul(q, y)),
                    sub(mul(y, add(t, y)), power(y, 2)),
                    add(sub(q, q), mul(y, t)), integer(0)]
        for rhs in examples:
            node = ode(rhs, initial_time=var('q'), initial_value=integer(0))
            result = analytic.normalize(node, {'q': 'real', 'x': 'real'})
            self.assertEqual(result['initial_time'], var('q'))
            self.assertEqual(result['initial_value'], integer(0))
            self.assertEqual(result['arg'], var('x'))
            for t_value, y_value in ((-2, 3), (0, 0), (2, -1)):
                values = {'t': Fraction(t_value), 'y': Fraction(y_value), 'q': Fraction(2)}
                coefficient = sum(evaluate(item, values) * values['t']**degree
                                  for degree, item in enumerate(result['coefficients']))
                self.assertEqual(coefficient * values['y'], evaluate(rhs, values))

    def test_ode_rejects_affine_nonlinear_or_state_dependent_denominators(self):
        t, y = var('t'), var('y')
        bad = [add(y, integer(1)), add(mul(t, y), t), power(y, 2), div(y, y), div(y, t),
               {'op': 'exp', 'arg': y}, {'op': 'deriv', 'var': 't', 'arg': y}]
        for rhs in bad:
            with self.subTest(rhs=rhs), self.assertRaises(InputError):
                analytic.normalize(ode(rhs), {'c': 'real', 'x': 'real'})

    def test_domain_scalars_survive_zero_cancellation_and_are_maximal_sorted_copies(self):
        quotient = div({'op': 'gamma', 'arg': var('q')}, var('q'))
        body = sub(mul(quotient, var('t')), mul(quotient, var('t')))
        node = integral(body, integer(0), var('x'))
        result = analytic.normalize(node, {'q': 'real', 'x': 'real'})
        self.assertEqual(result['coefficients'], [integer(0)])
        self.assertIn(quotient, result['scalar_expressions'])
        self.assertNotIn(var('q'), result['scalar_expressions'])
        self.assertEqual(result['scalar_expressions'].count(quotient), 1)
        keys = [json.dumps(item, sort_keys=True, separators=(',', ':')) for item in result['scalar_expressions']]
        self.assertEqual(keys, sorted(keys))
        self.assertIn(integer(0), result['scalar_expressions'])
        self.assertIn(var('x'), result['scalar_expressions'])
        scalar = analytic.normalize(ode(mul(var('q'), var('y'))), {'q': 'real', 'c': 'real', 'x': 'real'})
        for item in (var('q'), integer(-1), var('c'), var('x')):
            self.assertIn(item, scalar['scalar_expressions'])

    def test_constant_definitions_accept_zero_free_parameters(self):
        examples = [series(kernel(integer(2))),
                    integral(integer(3), integer(-1), integer(2)),
                    ode(mul(integer(2), var('y')), initial_time=integer(1),
                        initial_value=integer(3), arg=integer(-2))]
        results = [analytic.normalize(node, {}) for node in examples]
        self.assertEqual(results[0]['terms'], [{'coefficient': integer(1), 'argument': integer(2)}])
        self.assertEqual(results[1]['coefficients'], [integer(3)])
        self.assertEqual((results[1]['lower'], results[1]['upper']), (integer(-1), integer(2)))
        self.assertEqual(results[2]['coefficients'], [integer(2)])
        for node, result in zip(examples, results):
            with self.subTest(op=node['op']):
                self.assertEqual(result['original'], node)
                self.assertEqual(result, analytic.normalize(node, {'u': 'real'}))
        with self.assertRaises(InputError):
            analytic.normalize(series(kernel(var('u'))), {})

    def test_binders_and_parameters_reject_type_name_and_capture_conflicts(self):
        for parameters in ({'x': 'int'}, {'x': 'real', 'Xx': 'real', 'xx': 'real'},
                           {'a': 'real', 'b': 'real', 'c': 'real', 'e': 'real'}, {'bad-name': 'real'}):
            with self.subTest(parameters=parameters), self.assertRaises(InputError):
                analytic.normalize(integral(var('t')), parameters)
        for name in ('x', 'Xx', 'bad-name', 'π', '', 'a'*33, [], None):
            node = series(kernel(var('xx')), index=name)
            with self.subTest(name=name), self.assertRaises(InputError):
                analytic.normalize(node, {'x': 'real', 'xx': 'real'})
        for node in (ode(var('y'), state='t'), ode(var('y'), state='T'), ode(var('y'), var='c')):
            with self.subTest(node=node), self.assertRaises(InputError):
                analytic.normalize(node, {'c': 'real', 'x': 'real'})

    def test_endpoints_and_initial_data_cannot_capture_internal_variables(self):
        for field in ('lower', 'upper'):
            node = integral(var('t'))
            node[field] = var('t')
            with self.subTest(field=field), self.assertRaises(InputError):
                analytic.normalize(node, {'x': 'real'})
        for field in ('initial_time', 'initial_value', 'arg'):
            for bound in ('t', 'y'):
                node = ode(var('y'), **{field: var(bound)})
                with self.subTest(field=field, bound=bound), self.assertRaises(InputError):
                    analytic.normalize(node, {'c': 'real', 'x': 'real'})

    def test_strict_shapes_and_no_general_calculus_or_definition_injection(self):
        examples = [series(kernel(var('x'))), integral(var('t')), ode(var('y'))]
        for node in examples:
            for field in tuple(node):
                bad = deepcopy(node)
                del bad[field]
                with self.subTest(op=node['op'], missing=field), self.assertRaises(InputError):
                    analytic.normalize(bad, {'x': 'real', 'c': 'real'})
            for field in ('limit', 'first_index', 'assumptions', 'lean', 'coefficient'):
                with self.subTest(op=node['op'], extra=field), self.assertRaises(InputError):
                    analytic.normalize({**node, field: 'injected'}, {'x': 'real', 'c': 'real'})
        forbidden = [{'op': 'defined', 'function': 'a'*64, 'arguments': {'u': var('x')}},
                     {'op': 'deriv', 'var': 'x', 'arg': var('x')},
                     {'op': 'exp_series', 'arg': var('x')}, {'op': 'infinity'},
                     integral(var('t')), {'op': 'var', 'name': ['x']}]
        for expression in forbidden:
            with self.subTest(expression=expression), self.assertRaises(InputError):
                analytic.normalize(series(kernel(expression)), {'x': 'real'})
        for bad in (None, [], {}, {'op': []}, {'op': 3}, {1: 'bad'}):
            with self.subTest(bad=bad), self.assertRaises(InputError):
                analytic.normalize(bad, {'x': 'real'})

    def test_depth_size_cycles_and_malformed_nested_operations_raise_input_error(self):
        deep = var('t')
        for _ in range(25): deep = neg(deep)
        cycle = {'op': 'neg'}
        cycle['arg'] = cycle
        broad = {'op': 'add', 'args': [integer(1)]*1201}
        for body in (deep, cycle, broad, {'op': 'add', 'args': [var('t')]},
                     {'op': 'var', 'name': '\ud800'}, integer(True), {'op': []}):
            with self.subTest(kind=type(body).__name__), self.assertRaises(InputError):
                analytic.normalize(integral(body), {'x': 'real'})

    def test_determinism_and_original_input_are_isolated_from_every_output(self):
        node = integral(power(add(var('t'), var('q')), 2))
        before = deepcopy(node)
        first = analytic.normalize(node, {'q': 'real', 'x': 'real'})
        second = analytic.normalize(dict(reversed(list(node.items()))), {'x': 'real', 'q': 'real'})
        self.assertEqual(first, second)
        first['coefficients'][0].clear()
        self.assertEqual(first['original'], before)
        self.assertEqual(first['scalar_expressions'], second['scalar_expressions'])
        first['original']['integrand'].clear()
        first['scalar_expressions'].clear()
        self.assertEqual(node, before)
        self.assertEqual(analytic.normalize(node, {'q': 'real', 'x': 'real'}), second)


if __name__ == '__main__':
    unittest.main()
