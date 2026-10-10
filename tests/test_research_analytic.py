"""Analytic primitives fix their series, oriented interval, and global initial value."""
from copy import deepcopy
import json
import unittest

from special_function_agent import research_analytic as analytic
from special_function_agent.core import InputError


def var(name):
    return {'op': 'var', 'name': name}


def integer(value):
    return {'op': 'int', 'value': value}


def primitive(op):
    if op == 'linear_ivp':
        return {'op': op, 'rate': var('rate'), 'initial': var('initial'), 'arg': var('x')}
    return {'op': op, 'arg': var('x')}


class ResearchAnalyticTests(unittest.TestCase):
    def test_three_closed_shapes_and_exact_argument_order(self):
        self.assertEqual(analytic.OPS, {'exp_series', 'gaussian_primitive', 'linear_ivp'})
        self.assertEqual(analytic.fields(primitive('exp_series')), ('arg',))
        self.assertEqual(analytic.fields(primitive('gaussian_primitive')), ('arg',))
        self.assertEqual(analytic.fields(primitive('linear_ivp')), ('rate', 'initial', 'arg'))

    def test_unknown_fields_cannot_change_binder_limit_ode_or_initial_time(self):
        replacements = {'binder': 'u', 'limit': 12, 'lower': integer(1), 'upper': var('x'),
                        'initial_time': integer(1), 'equation': "y'=rate*y+1", 'term': var('x'),
                        'coefficient': var('x'), 'assumptions': ['x>0'], 'lean': 'axiom bad : False'}
        for op in sorted(analytic.OPS):
            for field, value in replacements.items():
                node = {**primitive(op), field: value}
                with self.subTest(op=op, field=field):
                    for method in (analytic.fields, analytic.expand, analytic.contracts):
                        with self.assertRaises(InputError):
                            method(node)
                    with self.assertRaises(InputError):
                        analytic.lean_expr(node, lambda _: 'unexpected')

    def test_missing_fields_and_nonexpression_arguments_are_rejected(self):
        for op in sorted(analytic.OPS):
            for field in analytic.fields(primitive(op)):
                node = primitive(op)
                del node[field]
                with self.subTest(op=op, field=field), self.assertRaises(InputError):
                    analytic.fields(node)
                for value in (None, [], 2, 'x'):
                    node = {**primitive(op), field: value}
                    with self.subTest(op=op, field=field, value=value), self.assertRaises(InputError):
                        analytic.fields(node)
        for node in (None, [], {}, {'op': []}, {'op': 'general_ode', 'arg': var('x')}):
            with self.subTest(node=node), self.assertRaises(InputError):
                analytic.fields(node)

    def test_nested_analytic_calls_and_unbounded_or_bound_children_are_rejected(self):
        excluded = [primitive(op) for op in sorted(analytic.OPS)] + [
            {'op': 'defined', 'function': 'f'*64, 'arguments': {'u': var('x')}},
            {'op': 'deriv', 'var': 'x', 'arg': var('x')},
            {'op': 'integral', 'var': 't', 'lower': integer(0), 'upper': var('x'), 'body': var('t')},
            {'op': 'infinity'}]
        for op in sorted(analytic.OPS):
            for field in analytic.fields(primitive(op)):
                for child in excluded:
                    node = {**primitive(op), field: {'op': 'add', 'args': [integer(1), child]}}
                    with self.subTest(op=op, field=field, child=child['op']), self.assertRaises(InputError):
                        analytic.fields(node)

    def test_expansion_preserves_coefficients_and_gaussian_normalization(self):
        x = var('x')
        self.assertEqual(analytic.expand(primitive('exp_series')), {'op': 'exp', 'arg': x})
        self.assertEqual(analytic.expand(primitive('gaussian_primitive')),
                         {'op': 'mul', 'args': [
                             {'op': 'div', 'args': [{'op': 'sqrt', 'arg': {'op': 'pi'}}, integer(2)]},
                             {'op': 'erf', 'arg': x}]})
        ivp = {'op': 'linear_ivp', 'rate': integer(-3), 'initial': integer(5), 'arg': x}
        self.assertEqual(analytic.expand(ivp), {'op': 'mul', 'args': [integer(5),
            {'op': 'exp', 'arg': {'op': 'mul', 'args': [integer(-3), x]}}]})

    def test_lean_calls_analytic_definitions_with_grouped_children_in_fixed_order(self):
        names = {'exp_series': 'exponentialSeries', 'gaussian_primitive': 'gaussianPrimitive',
                 'linear_ivp': 'homogeneousIVPSolution'}
        for op in sorted(analytic.OPS):
            seen = []
            def render(child):
                seen.append(child['name'])
                return 'rendered_'+child['name']
            text = analytic.lean_expr(primitive(op), render)
            expected = ['rate', 'initial', 'x'] if op == 'linear_ivp' else ['x']
            self.assertEqual(seen, expected)
            self.assertEqual(text, '(SpecialFunctionProofAgent.'+names[op]+' '+
                             ' '.join('(rendered_'+name+')' for name in expected)+')')
        text = analytic.lean_expr(primitive('exp_series'), lambda _: 'Real.rpow a b')
        self.assertEqual(text, '(SpecialFunctionProofAgent.exponentialSeries (Real.rpow a b))')

    def test_contracts_cover_all_real_arguments_and_negative_or_zero_endpoints(self):
        for op in sorted(analytic.OPS):
            for value in (-3, 0, 2):
                node = {**primitive(op), 'arg': integer(value)}
                if op == 'linear_ivp':
                    node.update(rate=integer(-1), initial=integer(0))
                contract = analytic.contracts(node)
                self.assertEqual(contract['domain'], {field: 'real' for field in analytic.fields(node)})
                self.assertEqual(contract['arguments'], {field: node[field] for field in analytic.fields(node)})
                self.assertEqual(contract['bridge'], analytic.rewrite_lemmas()[
                    ('exp_series', 'gaussian_primitive', 'linear_ivp').index(op)])
                self.assertNotIn('positive', json.dumps(contract))
        series = analytic.contracts(primitive('exp_series'))
        self.assertEqual(series['semantics'], {'index_domain': 'nat', 'first_index': 0,
                         'term': 'arg^n / n!', 'summation': 'infinite'})
        gaussian = analytic.contracts(primitive('gaussian_primitive'))
        self.assertEqual(gaussian['semantics']['lower_endpoint'], 0)
        self.assertEqual(gaussian['semantics']['upper_endpoint'], 'arg')
        self.assertEqual(gaussian['semantics']['orientation'], 'from_zero_to_arg')

    def test_ivp_contract_fixes_global_equation_initial_value_and_parameter_roles(self):
        contract = analytic.contracts(primitive('linear_ivp'))
        self.assertEqual(contract['kind'], 'unique_global_ivp_solution')
        self.assertEqual(contract['semantics']['time_domain'], 'real')
        self.assertEqual(contract['semantics']['equation'], "y'(t) = rate*y(t)")
        self.assertEqual(contract['semantics']['initial_condition'], {'time': 0, 'value': 'initial'})
        self.assertEqual(contract['semantics']['fixed_parameters'], ['rate', 'initial'])
        self.assertEqual(contract['semantics']['evaluation_argument'], 'arg')
        self.assertEqual(contract['theorems'], ['SpecialFunctionProofAgent.'+name for name in (
            'hasDerivAt_homogeneousIVPSolution', 'homogeneousIVPSolution_zero',
            'homogeneousIVPSolution_unique', 'existsUnique_homogeneousIVPSolution')])

    def test_deterministic_metadata_and_expansion_do_not_alias_input(self):
        for op in sorted(analytic.OPS):
            node = primitive(op)
            before = deepcopy(node)
            expanded = analytic.expand(node)
            contract = analytic.contracts(node)
            self.assertEqual(contract, analytic.contracts(dict(reversed(list(node.items())))))
            contract['arguments']['arg']['name'] = 'changed'
            contract['theorems'].append('unknown')
            expanded.clear()
            self.assertEqual(node, before)
            self.assertNotIn('unknown', analytic.contracts(node)['theorems'])
        lemmas = analytic.rewrite_lemmas()
        lemmas.clear()
        self.assertEqual(len(analytic.rewrite_lemmas()), 3)

    def test_deep_and_cyclic_child_objects_raise_input_error(self):
        node = primitive('exp_series')
        child = node['arg']
        child['cycle'] = child
        with self.assertRaises(InputError):
            analytic.fields(node)


if __name__ == '__main__':
    unittest.main()
