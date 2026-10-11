"""The four additional analytic grammars preserve their original parameters."""
from copy import deepcopy
from fractions import Fraction
import json
import math
import unittest

from special_function_agent import research_advanced_analytic as analytic
from special_function_agent import research_user_analytic as previous
from special_function_agent.core import InputError


def integer(value): return {'op': 'int', 'value': value}
def var(name): return {'op': 'var', 'name': name}
def binary(op, left, right): return {'op': op, 'args': [left, right]}
def add(left, right): return binary('add', left, right)
def sub(left, right): return binary('sub', left, right)
def mul(left, right): return binary('mul', left, right)
def div(left, right): return binary('div', left, right)
def unary(op, arg): return {'op': op, 'arg': arg}
def neg(arg): return unary('neg', arg)
def power(base, exponent): return {'op': 'pow', 'base': base, 'exponent': exponent}
def geometric(base, index='k'): return power(base, var(index))
def bounded(argument): return div(argument, add(integer(1), power(argument, 2)))
def state_kernel(): return unary('sqrt', add(integer(1), power(var('y'), 2)))
def series(term, **kwargs):
    return {'op': 'geometric_series_definition', 'index': 'k', 'term': term, **kwargs}
def integral(body, **kwargs):
    return {'op': 'elementary_integral_definition', 'var': 't', 'integrand': body,
            'lower': integer(-2), 'upper': var('x'), **kwargs}
def nonlinear(rhs, **kwargs):
    return {'op': 'nonlinear_ode_definition', 'var': 't', 'state': 'y', 'rhs': rhs,
            'initial_time': integer(-1), 'initial_value': var('c'), 'arg': var('x'), **kwargs}
def second_order(rhs, **kwargs):
    return {'op': 'second_order_ode_definition', 'var': 't', 'state': 'y', 'velocity': 'v',
            'rhs': rhs, 'initial_time': integer(-2), 'initial_value': var('c'),
            'initial_derivative': integer(3), 'arg': var('x'), **kwargs}


def evaluate(node, values):
    op = node['op']
    if op == 'int': return Fraction(node['value'])
    if op == 'var': return values[node['name']]
    if op == 'neg': return -evaluate(node['arg'], values)
    if op in {'exp', 'sin', 'cos', 'sqrt'}:
        return getattr(math, op)(evaluate(node['arg'], values))
    if op == 'pow':
        exponent = node['exponent']
        return evaluate(node['base'], values) ** (evaluate(exponent, values) if isinstance(exponent, dict) else exponent)
    left, right = (evaluate(child, values) for child in node['args'])
    return {'add': lambda: left + right, 'sub': lambda: left - right,
            'mul': lambda: left * right, 'div': lambda: left / right}[op]()


class AdvancedAnalyticTests(unittest.TestCase):
    def test_geometric_fixed_rational_terms_preserve_original_values(self):
        half = div(integer(1), integer(2))
        bases = [integer(0), half, neg(half), div(sub(integer(5), integer(7)), integer(3))]
        term = add(mul(var('c'), geometric(bases[1])), div(neg(geometric(bases[2])), integer(2)))
        for body in [geometric(base) for base in bases] + [term]:
            with self.subTest(body=body):
                result = analytic.normalize(series(body), {'c': 'real'})
                for k in range(6):
                    values = {'k': k, 'c': Fraction(-3)}
                    actual = sum(evaluate(item['coefficient'], values) * evaluate(item['argument'], values)**k
                                 for item in result['terms'])
                    self.assertEqual(actual, evaluate(body, values))
                for item in result['terms']:
                    self.assertEqual(item['base_kind'], 'rational')
                    value = Fraction(**item['base_value'])
                    self.assertEqual(value, evaluate(item['argument'], {}))
                    self.assertLess(abs(value), 1)

    def test_geometric_bounded_bases_retain_exact_argument_and_sign(self):
        u = add(var('a'), integer(2))
        bases = [bounded(u), neg(bounded(u)), div(neg(u), add(power(u, 2), integer(1))),
                 div(u, add(integer(1), mul(neg(u), neg(u))))]
        for base, sign in zip(bases, (1, -1, -1, 1)):
            with self.subTest(base=base):
                result = analytic.normalize(series(geometric(base)), {'a': 'real'})
                item = result['terms'][0]
                self.assertEqual(item['argument'], base)
                self.assertEqual((item['base_kind'], item['base_argument'], item['base_sign']),
                                 ('bounded_rational', u, sign))
                self.assertEqual(result['required_conditions'], [{'kind': 'abs_lt_one', 'argument': base}])
                for a in (-10, -2, 0, 7):
                    self.assertLess(abs(evaluate(base, {'a': Fraction(a)})), 1)

    def test_geometric_rejects_unsupported_bases_even_when_cancelled(self):
        bad_bases = [integer(1), integer(-1), integer(2), var('a'),
                     div(var('a'), add(integer(2), power(var('a'), 2))),
                     div(integer(1), integer(0)), div(integer(1), mul(integer(1000), integer(2)))]
        for base in bad_bases:
            for body in (geometric(base), mul(integer(0), geometric(base)),
                         sub(geometric(base), geometric(base))):
                with self.subTest(body=body), self.assertRaises(InputError):
                    analytic.normalize(series(body), {'a': 'real'})
        for body in (integer(1), power(div(integer(1), integer(2)), add(var('k'), integer(1))),
                     div(geometric(integer(0)), var('k')), mul(geometric(integer(0)), geometric(integer(0)))):
            with self.subTest(body=body), self.assertRaises(InputError):
                analytic.normalize(series(body), {})

    def test_elementary_affine_arguments_reconstruct_each_original_argument(self):
        t, b = var('t'), var('b')
        arguments = [add(mul(integer(2), t), b), div(sub(b, t), integer(2)),
                     add(sub(t, t), b), sub(mul(add(t, integer(1)), integer(3)), t)]
        for kind in ('exp', 'sin', 'cos'):
            for argument in arguments:
                body = div(mul(var('c'), unary(kind, argument)), integer(2))
                with self.subTest(kind=kind, argument=argument):
                    result = analytic.normalize(integral(body, lower=var('x'), upper=integer(-3)),
                                                {'b': 'real', 'c': 'real', 'x': 'real'})
                    self.assertEqual((result['lower'], result['upper']), (var('x'), integer(-3)))
                    self.assertEqual(result['terms'][0]['kind'], kind)
                    self.assertEqual(len(result['affine_arguments']), 1)
                    affine = result['affine_arguments'][0]
                    self.assertEqual(affine['original'], argument)
                    for value in (-2, 0, 3):
                        values = {'t': Fraction(value), 'b': Fraction(2), 'c': Fraction(-1), 'x': Fraction(-4)}
                        normalized = evaluate(affine['slope'], values)*values['t'] + evaluate(affine['intercept'], values)
                        self.assertEqual(normalized, evaluate(argument, values))
                        actual = sum(evaluate(item['coefficient'], values) * getattr(math, item['kind'])(
                            evaluate(item['slope'], values)*values['t'] + evaluate(item['intercept'], values))
                            for item in result['terms'])
                        self.assertAlmostEqual(actual, evaluate(body, values))

    def test_elementary_zero_slope_and_cancelled_affine_metadata(self):
        argument = add(sub(var('t'), var('t')), var('b'))
        kernel = unary('cos', argument)
        body = add(mul(integer(0), kernel), sub(kernel, kernel))
        result = analytic.normalize(integral(body), {'b': 'real', 'x': 'real'})
        self.assertEqual(result['affine_arguments'], [{'original': argument, 'slope': integer(0), 'intercept': var('b')}])
        self.assertEqual([item['slope'] for item in result['terms']], [integer(0)]*3)
        self.assertEqual(result['required_conditions'], [])
        self.assertEqual(result['nonzero_denominators'], [])
        self.assertEqual(analytic.normalize(integral(unary('exp', var('b'))), {'b': 'real', 'x': 'real'})['terms'][0]['slope'], integer(0))

    def test_elementary_excludes_parameter_slopes_and_nonlinear_time(self):
        t = var('t')
        bad = [unary('sin', mul(var('a'), t)), unary('exp', power(t, 2)), unary('cos', div(t, var('a'))),
               unary('exp', unary('sin', t)), mul(unary('sin', t), unary('cos', t)),
               div(unary('exp', t), t), add(unary('exp', t), t)]
        for body in bad:
            with self.subTest(body=body), self.assertRaises(InputError):
                analytic.normalize(integral(body), {'a': 'real', 'x': 'real'})

    def test_nonlinear_rhs_preserves_polynomial_factor_and_initial_data(self):
        t, kernel = var('t'), state_kernel()
        alternate = unary('sqrt', add(mul(var('y'), var('y')), integer(1)))
        bodies = [mul(add(power(t, 2), var('a')), kernel),
                  sub(add(mul(t, kernel), mul(kernel, t)), mul(var('a'), alternate)),
                  mul(power(add(t, var('a')), 2), alternate), integer(0)]
        for body in bodies:
            node = nonlinear(body, initial_time=var('a'), initial_value=integer(0))
            result = analytic.normalize(node, {'a': 'real', 'x': 'real'})
            self.assertEqual((result['initial_time'], result['initial_value'], result['arg']), (var('a'), integer(0), var('x')))
            for time, state in ((-2, 3), (0, 0), (2, -1)):
                values = {'t': Fraction(time), 'y': Fraction(state), 'a': Fraction(2), 'x': Fraction(-1)}
                coefficient = sum(evaluate(item, values)*values['t']**degree for degree, item in enumerate(result['coefficients']))
                self.assertAlmostEqual(coefficient*math.sqrt(1+state**2), evaluate(body, values))

    def test_nonlinear_excludes_other_state_kernels_and_unbound_synthetic_names(self):
        y, t, kernel = var('y'), var('t'), state_kernel()
        bad = [y, add(kernel, integer(1)), mul(kernel, kernel), div(kernel, y), div(kernel, t),
               unary('sqrt', sub(integer(1), power(y, 2))),
               unary('sqrt', add(integer(1), power(add(y, integer(1)), 2))),
               add(kernel, var('analyticKernel0')), mul(var('analyticKernel1'), kernel)]
        for body in bad:
            with self.subTest(body=body), self.assertRaises(InputError):
                analytic.normalize(nonlinear(body), {'c': 'real', 'x': 'real'})
        result = analytic.normalize(nonlinear(mul(var('analyticKernel0'), kernel)),
                                    {'analyticKernel0': 'real', 'c': 'real', 'x': 'real'})
        self.assertEqual(result['coefficients'], [var('analyticKernel0')])

    def test_second_order_forcing_and_degree_preserve_position_velocity_roles(self):
        t = var('t')
        bodies = [integer(0), add(power(t, 2), var('a')), power(t, 12), div(power(add(t, var('a')), 3), integer(2))]
        for body in bodies:
            node = second_order(body, initial_time=integer(-7), initial_value=integer(0), initial_derivative=var('a'))
            result = analytic.normalize(node, {'a': 'real', 'x': 'real'})
            self.assertEqual((result['state'], result['velocity']), ('y', 'v'))
            self.assertEqual((result['initial_time'], result['initial_value'], result['initial_derivative']),
                             (integer(-7), integer(0), var('a')))
            for time in (-2, 0, 3):
                values = {'t': Fraction(time), 'a': Fraction(2), 'x': Fraction(3)}
                actual = sum(evaluate(item, values)*values['t']**degree for degree, item in enumerate(result['coefficients']))
                self.assertEqual(actual, evaluate(body, values))
        bad = [var('y'), var('v'), sub(var('y'), var('y')), sub(var('v'), var('v')),
               power(t, 13), mul(power(t, 7), power(t, 6)), unary('exp', t)]
        for body in bad:
            with self.subTest(body=body), self.assertRaises(InputError):
                analytic.normalize(second_order(body), {'c': 'real', 'x': 'real'})

    def test_cancelled_domain_scalars_and_denominators_are_retained(self):
        gamma = unary('gamma', var('a'))
        half = div(integer(1), integer(2))
        elementary = unary('sin', div(var('t'), integer(2)))
        cases = [series(mul(integer(0), div(mul(gamma, geometric(half)), var('a')))),
                 integral(sub(div(mul(gamma, elementary), var('a')), div(mul(gamma, elementary), var('a')))),
                 nonlinear(sub(div(mul(gamma, state_kernel()), var('a')), div(mul(gamma, state_kernel()), var('a')))),
                 second_order(sub(div(mul(gamma, var('t')), var('a')), div(mul(gamma, var('t')), var('a'))))]
        for node in cases:
            with self.subTest(op=node['op']):
                result = analytic.normalize(node, {'a': 'real', 'c': 'real', 'x': 'real'})
                self.assertIn(gamma, result['scalar_expressions'])
                self.assertIn(var('a'), result['nonzero_denominators'])
                self.assertEqual(result['nonzero_denominators'].count(var('a')), 1)
                if 'coefficients' in result: self.assertEqual(result['coefficients'], [integer(0)])
                if node['op'] == 'geometric_series_definition':
                    self.assertEqual(result['terms'][0]['coefficient'], integer(0))
                    self.assertEqual(result['required_conditions'], [{'kind': 'abs_lt_one', 'argument': half}])

    def test_kernel_count_and_exact_arithmetic_are_bounded_before_cancellation(self):
        for kernel, constructor, parameters in ((geometric(integer(0)), series, {}),
                (unary('sin', var('t')), integral, {'x': 'real'}),
                (state_kernel(), nonlinear, {'c': 'real', 'x': 'real'})):
            body = kernel
            for _ in range(15): body = add(body, kernel)
            constructor_result = analytic.normalize(constructor(body), parameters)
            self.assertEqual(constructor_result['original'], constructor(body))
            with self.assertRaisesRegex(InputError, '16'):
                analytic.normalize(constructor(mul(integer(0), add(body, kernel))), parameters)
        huge = integer(1000)
        for _ in range(7): huge = mul(huge, integer(1000))
        with self.assertRaisesRegex(InputError, '64-bit'):
            analytic.normalize(series(geometric(div(integer(1), huge))), {})
        deep = var('t')
        for _ in range(25): deep = neg(deep)
        cycle = {'op': 'neg'}
        cycle['arg'] = cycle
        broad = {'op': 'add', 'args': [integer(0)]*1201}
        for body in (deep, cycle, broad):
            with self.subTest(kind=type(body).__name__), self.assertRaises(InputError):
                analytic.normalize(second_order(body), {'c': 'real', 'x': 'real'})

    def test_binders_types_and_external_data_prevent_capture(self):
        samples = [series(geometric(integer(0))), integral(unary('cos', var('t'))),
                   nonlinear(state_kernel()), second_order(var('t'))]
        for node in samples:
            for parameters in ({'x': 'nat'}, {'a': 'real', 'b': 'real', 'c': 'real', 'e': 'real'},
                               {'bad-name': 'real'}, {'xx': 'real', 'Xx': 'real'}):
                with self.subTest(op=node['op'], parameters=parameters), self.assertRaises(InputError):
                    analytic.normalize(node, parameters)
            for binder in ('index', 'var', 'state', 'velocity'):
                if binder not in node: continue
                for name in ('x', 'X', 'π', 'bad-name', [], ''):
                    with self.subTest(op=node['op'], binder=binder, name=name), self.assertRaises(InputError):
                        analytic.normalize({**node, binder: name}, {'x': 'real', 'c': 'real'})
            for field in ('lower', 'upper', 'initial_time', 'initial_value', 'initial_derivative', 'arg'):
                if field not in node: continue
                with self.subTest(op=node['op'], field=field), self.assertRaises(InputError):
                    analytic.normalize({**node, field: var(node['var'])}, {'x': 'real', 'c': 'real'})
        for field, value in (('state', 'T'), ('velocity', 'Y'), ('velocity', 't')):
            with self.subTest(field=field), self.assertRaises(InputError):
                analytic.normalize(second_order(var('t'), **{field: value}), {'x': 'real', 'c': 'real'})

    def test_strict_fields_and_nested_unsupported_expressions_raise_input_error(self):
        samples = [series(geometric(integer(0))), integral(unary('cos', var('t'))),
                   nonlinear(state_kernel()), second_order(var('t'))]
        for node in samples:
            for field in node:
                bad = deepcopy(node)
                del bad[field]
                with self.subTest(op=node['op'], missing=field), self.assertRaises(InputError):
                    analytic.normalize(bad, {'x': 'real', 'c': 'real'})
            for field in ('limit', 'assumptions', 'lean', 'initial_acceleration'):
                with self.subTest(op=node['op'], extra=field), self.assertRaises(InputError):
                    analytic.normalize({**node, field: 'injected'}, {'x': 'real', 'c': 'real'})
        bad = [{'op': []}, {'op': 'int'}, {'op': 'add', 'args': [integer(0)]}, integer(True),
               {'op': 'defined', 'function': 'a'*64, 'arguments': {}},
               {'op': 'deriv', 'var': 'x', 'arg': var('x')}, {'op': 'exp_series', 'arg': var('x')}]
        for body in bad:
            for node in (series(geometric(body)), integral(mul(integer(0), body)), nonlinear(mul(body, state_kernel()))):
                with self.subTest(node=node), self.assertRaises(InputError):
                    analytic.normalize(node, {'x': 'real', 'c': 'real'})

    def test_zero_parameter_definitions_and_original_snapshots_are_independent(self):
        nodes = [series(geometric(div(integer(1), integer(2)))),
                 integral(unary('exp', integer(2)), upper=integer(1)),
                 nonlinear(state_kernel(), initial_value=integer(0), arg=integer(-3)),
                 second_order(integer(4), initial_value=integer(0), arg=integer(-3))]
        for node in nodes:
            before = deepcopy(node)
            first = analytic.normalize(node, {})
            second = analytic.normalize(dict(reversed(list(node.items()))), {'u': 'real'})
            self.assertEqual(first, second)
            for field in ('scalar_expressions', 'nonzero_denominators', 'required_conditions', 'affine_arguments'):
                if field not in first: continue
                keys = [json.dumps(item, sort_keys=True, separators=(',', ':')) for item in first[field]]
                self.assertEqual(keys, sorted(set(keys)))
                first[field].clear()
            self.assertEqual(first['original'], before)
            first['original'].clear()
            self.assertEqual(node, before)
            self.assertEqual(analytic.normalize(node, {}), second)

    def test_legacy_normalization_is_unchanged_by_advanced_calls(self):
        node = {'op': 'integral_definition', 'var': 't', 'integrand': add(power(var('t'), 2), integer(1)),
                'lower': integer(-2), 'upper': var('x')}
        before = previous.normalize(node, {'x': 'real'})
        analytic.normalize(integral(unary('sin', var('t'))), {'x': 'real'})
        self.assertEqual(previous.normalize(node, {'x': 'real'}), before)
        self.assertEqual(before['coefficients'], [integer(1), integer(0), integer(1)])
        self.assertNotIn('required_conditions', before)
        self.assertNotIn('affine_arguments', before)


if __name__ == '__main__':
    unittest.main()
