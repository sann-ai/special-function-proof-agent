"""Integer Y argument calculus keeps the original variable, domain, and evidence."""
from copy import deepcopy
from importlib import import_module
import json
import importlib.util
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from special_function_agent import archive
from special_function_agent.bessel_y_integer import formal_scope
from special_function_agent.core import ALLOWED_AXIOMS, InputError, ROOT, _run_lean, replay, verify, validate_request
from special_function_agent.generate import make_prompt, output_schema
from special_function_agent.parser import parse_identity
from special_function_agent.real_special import default_proof, has_special, match_identity, render
from special_function_agent.real_numeric import diagnose

EXAMPLES = ('integer-y-zero-derivative', 'integer-y-one-derivative')
WRONSKIAN_EXAMPLES = ('integer-y-wronskian', 'integer-y-cross-same-point')
ACCEPTED = {'accepted': True, 'axioms': sorted(ALLOWED_AXIOMS)}


def request(name=EXAMPLES[0], route='direct'):
    data = parse_identity((ROOT/f'examples/{name}.txt').read_text())
    return {**data, 'proof': default_proof(data, route)}


def without_mpmath(name, *args, **kwargs):
    if name == 'mpmath':
        raise ImportError('optional numerical backend unavailable')
    return import_module(name, *args, **kwargs)


class IntegerYCalculusBoundaryTests(unittest.TestCase):
    def test_fixed_examples_and_standard_definition_have_no_extra_analytic_premises(self):
        for name in EXAMPLES:
            target = json.loads((ROOT/f'examples/{name}.target.json').read_text())
            for route in ('direct', 'steps'):
                data = request(name, route)
                self.assertEqual({k: v for k, v in data.items() if k != 'proof'}, target)
                self.assertEqual(data['variables'], {'x': 'real'})
                validate_request(data)
                self.assertTrue(has_special(data))
                source = render(data)
                self.assertIn('SpecialFunctionProofAgent.besselYInt', source)
                self.assertIn('SpecialFunctionProofAgent.deriv_besselYInt_', source)
                self.assertNotIn('DifferentiableAt', source)
                self.assertNotIn('HasDerivAt', source)
                self.assertEqual(source.count('(h0 :'), 1)

    def test_derivative_variable_composition_coefficient_and_order_are_fixed(self):
        false = (
            'D_r(Y_0(x))=-Y_1(x);r real,x>0',
            'D_x(Y_0(2*x))=-Y_1(2*x);x>0',
            'D_x(Y_0(x))=Y_1(x);x>0',
            'D_x(Y_0(x))=-Y_2(x);x>0',
            'D_x(Y_1(x))=Y_0(x)-2*Y_1(x)/x;x>0',
            'D_x(D_x(Y_0(x)))=-Y_1(x);x>0',
        )
        for text in false:
            with self.subTest(text=text):
                data = parse_identity(text)
                self.assertIsNone(match_identity(data['lhs'], data['rhs']))
                self.assertFalse(has_special(data))
                data['proof'] = {'mode': 'direct', 'recipe': 'integer_y_derivative'}
                with self.assertRaises(InputError):
                    validate_request(data)

    def test_nonpositive_or_missing_domain_preserves_target_and_stops_before_lean(self):
        for condition in ('x real', 'x>=0', 'x=0', 'x<0'):
            data = parse_identity('D_x(Y_0(x))=-Y_1(x);'+condition)
            data['proof'] = default_proof(data)
            with self.subTest(condition=condition), tempfile.TemporaryDirectory() as tmp, \
                 patch('special_function_agent.real_numeric.importlib.import_module', side_effect=without_mpmath), \
                 patch('special_function_agent.real_special._run_lean') as lean:
                result = verify(data, Path(tmp)/'run', timeout=120)
                self.assertEqual(result['status'], 'needs_conditions')
                self.assertFalse(result['full_bessel_proof'])
                self.assertEqual(json.loads((Path(tmp)/'run/request.json').read_text()), data)
                lean.assert_not_called()

    def test_names_reverse_and_all_extra_conditions_are_preserved(self):
        data = parse_identity('-Y_1(d1)=D_d1(Y_0(d1));d1>0,d1<5,r real')
        data['proof'] = default_proof(data, 'steps')
        self.assertTrue(match_identity(data['lhs'], data['rhs'])['reverse'])
        source = render(data)
        self.assertIn(').symm', source)
        self.assertIn('(h1 : v0 < (5 / 1 : ℝ))', source)
        self.assertIn('(deriv (fun (d2 : ℝ)', source)
        self.assertIn('(v1 : ℝ)', source)

    def test_ai_cannot_replace_target_or_supply_exchange_assumptions(self):
        data = request(route='steps')
        schema = output_schema('steps', data)
        self.assertIn('integer_y_derivative', schema['properties']['steps']['items']['properties']['recipe']['enum'])
        self.assertNotIn('assumptions', schema['properties'])
        self.assertIn('integer_y_derivative', make_prompt(data, 'steps'))
        for change in ('condition', 'target', 'premise'):
            modified = deepcopy(data)
            if change == 'condition':
                modified['proof']['steps'][0]['conditions'].append('mixed derivative exchange')
            elif change == 'target':
                modified['proof']['steps'][0]['after'] = {'op': 'int', 'value': 0}
            else:
                modified['proof']['assumptions'] = ['J is twice differentiable']
            with self.subTest(change=change), self.assertRaises(InputError):
                validate_request(modified)

    def test_saved_new_scope_source_and_flags_reject_tampering(self):
        with tempfile.TemporaryDirectory() as tmp, \
             patch('special_function_agent.real_numeric.importlib.import_module', side_effect=without_mpmath), \
             patch('special_function_agent.real_special._run_lean', return_value=ACCEPTED) as lean:
            for change in ('scope', 'source', 'request', 'proof-status'):
                output = Path(tmp)/change
                data = request()
                result = verify(data, output, timeout=120)
                self.assertEqual(result['formal_scope'], formal_scope(data))
                if change == 'source':
                    path = output/'certificate.lean'
                    path.write_text(path.read_text()+'\n-- changed\n')
                elif change == 'request':
                    path = output/'request.json'
                    altered = deepcopy(data)
                    altered['assumptions'] = []
                    path.write_text(json.dumps(altered))
                else:
                    result['formal_scope' if change == 'scope' else 'full_bessel_proof'] = 'wrong' if change == 'scope' else False
                    (output/'result.json').write_text(json.dumps(result))
                lean.reset_mock()
                with self.subTest(change=change), self.assertRaises(InputError):
                    replay(output, timeout=120)
                lean.assert_not_called()


class IntegerYWronskianBoundaryTests(unittest.TestCase):
    def test_positive_wronskian_and_negative_same_point_cross_match_original_definition(self):
        for name in WRONSKIAN_EXAMPLES:
            for route in ('direct', 'steps'):
                data = request(name, route)
                self.assertTrue(has_special(data))
                validate_request(data)
                source = render(data)
                self.assertIn('SpecialFunctionProofAgent.realBesselJ', source)
                self.assertIn('SpecialFunctionProofAgent.besselYInt', source)
                self.assertNotIn('DifferentiableAt', source)
                self.assertNotIn('HasDerivAt', source)
                self.assertEqual(data['assumptions'], parse_identity('Y_0(x)=Y_0(x);x>0')['assumptions'])
                if name.endswith('same-point'):
                    self.assertIn('besselYInt_cross_zero_one', source)
                    self.assertIn('(-2 : ℝ)', source)
                    self.assertEqual(data['lhs'], {'op': 'bessel_cross',
                        'orders': [{'op': 'int', 'value': 0}, {'op': 'int', 'value': 1}],
                        'args': [{'op': 'var', 'name': 'x'}]*2})
        expanded = parse_identity('J_0(x)*Y_1(x)-Y_0(x)*J_1(x)=-2/(pi*x);x>0')
        self.assertTrue(has_special(expanded))
        self.assertEqual(match_identity(expanded['lhs'], expanded['rhs'])['theorem'], 'besselYInt_cross_zero_one')

    def test_sign_coefficient_orders_and_distinct_arguments_do_not_match(self):
        for text in ('X_01(x,x)=2/(pi*x);x>0', 'X_10(x,x)=-2/(pi*x);x>0',
                     'X_01(x,z)=-2/(pi*x);x>0,z>0', 'X_01(x,x)=-3/(pi*x);x>0',
                     'J_1(x)*Y_0(x)-J_0(x)*Y_1(x)=-2/(pi*x);x>0'):
            with self.subTest(text=text):
                data = parse_identity(text)
                self.assertFalse(has_special(data))
                self.assertIsNone(match_identity(data['lhs'], data['rhs']))

    def test_cross_root_target_and_legacy_diagnostic_route_keep_their_scope(self):
        target = parse_identity((ROOT/'examples/cross-product-root.txt').read_text())
        self.assertFalse(has_special({**target, 'proof': {'mode': 'diagnostic'}}))
        self.assertEqual(target['lhs']['args'][1]['args'][1]['args'][1]['orders'],
                         [{'op': 'int', 'value': 0}, {'op': 'int', 'value': 2}])
        target = request(WRONSKIAN_EXAMPLES[1], 'diagnostic')
        self.assertFalse(has_special(target))
        for name in WRONSKIAN_EXAMPLES:
            for condition in ('x real', 'x>=0', 'x=0'):
                changed = parse_identity((ROOT/f'examples/{name}.txt').read_text().replace('x>0', condition))
                changed['proof'] = default_proof(changed)
                with tempfile.TemporaryDirectory() as tmp, \
                     patch('special_function_agent.real_numeric.importlib.import_module', side_effect=without_mpmath), \
                     patch('special_function_agent.real_special._run_lean') as lean:
                    result = verify(changed, Path(tmp)/'run', timeout=120)
                    self.assertEqual(result['status'], 'needs_conditions', result)
                    lean.assert_not_called()


@unittest.skipUnless(importlib.util.find_spec('mpmath'), 'Uses the existing optional mpmath runtime.')
class IntegerYCalculusNumericalTests(unittest.TestCase):
    def test_derivatives_and_both_wronskian_signs_agree_on_positive_samples(self):
        for name in EXAMPLES + WRONSKIAN_EXAMPLES:
            with self.subTest(name=name):
                result = diagnose(request(name))
                self.assertEqual(result['diagnostic'], 'no_mismatch_found', result)
                self.assertGreater(result['checked_samples'], 0)
                self.assertFalse(result['full_bessel_proof'])

    def test_wrong_cross_sign_and_wrong_derivative_coefficient_give_mismatch(self):
        for text in ('X_01(x,x)=2/(pi*x);x>0', 'D_x(Y_0(x))=-2*Y_1(x);x>0'):
            with self.subTest(text=text):
                result = diagnose(parse_identity(text))
                self.assertEqual(result['diagnostic'], 'counterexample_candidates', result)
                self.assertGreater(len(result['candidates']), 0)
                self.assertFalse(result['full_bessel_proof'])


@unittest.skipUnless(os.environ.get('SF_RUN_LEAN_TESTS') == '1', 'Enable integer-Y calculus Lean acceptance.')
class IntegerYCalculusLeanTests(unittest.TestCase):
    def test_both_formulas_both_routes_replay_with_no_optional_numerics(self):
        with tempfile.TemporaryDirectory() as tmp, \
             patch('special_function_agent.real_numeric.importlib.import_module', side_effect=without_mpmath):
            for name in EXAMPLES + WRONSKIAN_EXAMPLES:
                for route in ('direct', 'steps'):
                    with self.subTest(name=name, route=route):
                        output = Path(tmp)/(name+'-'+route)
                        result = verify(request(name, route), output, timeout=120)
                        self.assertEqual(result['status'], 'proved', result)
                        self.assertTrue(result['full_bessel_proof'])
                        self.assertEqual(result['numerical']['diagnostic'], 'backend_unavailable')
                        self.assertTrue(set(result['attempts'][0]['axioms']) <= ALLOWED_AXIOMS)
                        self.assertTrue(replay(output, timeout=120)['replayed'])
            record = archive.register_verification(output, Path(tmp)/'archive', timeout=120)
            self.assertTrue(archive.replay_record(record['id'], Path(tmp)/'archive', timeout=120)['replayed'])

    def test_named_reverse_and_negative_binding_cases_pass_through_kernel(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            target = parse_identity('-Y_1(radius)=D_radius(Y_0(radius));radius>0,radius<3')
            target['proof'] = default_proof(target, 'steps')
            result = verify(target, base/'reverse', timeout=120)
            self.assertEqual(result['status'], 'proved', result)
            for index, text in enumerate((
                'D_r(Y_0(x))=-Y_1(x);r real,x>0',
                'D_x(Y_0(2*x))=-Y_1(2*x);x>0',
                'D_x(D_x(Y_0(x)))=-Y_1(x);x>0',
            )):
                target = parse_identity(text)
                target['proof'] = {'mode': 'direct', 'recipe': 'ring'}
                path = base/f'negative-{index}.lean'
                path.write_text(render(target))
                self.assertFalse(_run_lean(path, timeout=120)['accepted'], text)


if __name__ == '__main__':
    unittest.main()
