"""The original cross root identity requires its root and positive energy domain."""
from copy import deepcopy
from importlib import import_module
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from special_function_agent import archive
from special_function_agent.core import ALLOWED_AXIOMS, InputError, ROOT, _run_lean, replay, validate_request, verify
from special_function_agent.cross_complete import complete_target, match_identity, FORMAL_SCOPE
from special_function_agent.generate import make_prompt, output_schema
from special_function_agent.parser import parse_identity
from special_function_agent.real_special import default_proof, has_special, render

TEXT = (ROOT/'examples/cross-product-root.txt').read_text()
ACCEPTED = {'accepted': True, 'axioms': sorted(ALLOWED_AXIOMS)}


def request(text=TEXT, route='direct'):
    target = parse_identity(text)
    return {**target, 'proof': default_proof(target, route)}


def without_mpmath(name, *args, **kwargs):
    if name == 'mpmath':
        raise ImportError('optional backend unavailable')
    return import_module(name, *args, **kwargs)


class CrossCompleteBoundaryTests(unittest.TestCase):
    def test_original_target_id_and_all_conditions_are_fixed(self):
        data = request()
        old = json.loads((ROOT/'demo/cross-product/request.json').read_text())
        target = json.loads((ROOT/'examples/cross-product-root.target.json').read_text())
        self.assertEqual({k: v for k, v in data.items() if k != 'proof'}, target)
        self.assertEqual(archive.target_hash(data), archive.target_hash(old))
        self.assertEqual(data['assumptions'], old['assumptions'])
        self.assertEqual(len(data['assumptions']), 4)
        self.assertTrue(complete_target(data))
        self.assertEqual(data['lhs']['args'][1]['args'][1]['args'][1]['orders'],
                         [{'op': 'int', 'value': 0}, {'op': 'int', 'value': 2}])
        for route in ('direct', 'steps'):
            fixed = request(route=route)
            validate_request(fixed)
            source = render(fixed)
            self.assertIn('besselCross_root_left_denominator_pos', source)
            self.assertIn('besselCross_root_right_denominator_ne_zero', source)
            self.assertIn('besselCross_root_identity', source)
            self.assertNotIn('DifferentiableAt', source)
            self.assertNotIn('HasDerivAt', source)
            self.assertNotIn('deriv (', source)
            statement = source.split(' := by', 1)[0]
            self.assertEqual(statement.count('(h'), 4)

    def test_missing_root_or_scalar_bounds_do_not_gain_a_full_recipe(self):
        cases = (TEXT.replace(', X_01(z,lambda*z) = 0', ''),
                 TEXT.replace('0 < lambda < 1', 'lambda > 0'),
                 TEXT.replace('0 < lambda < 1', '0 < lambda <= 1'),
                 TEXT.replace('0 < lambda < 1', 'lambda = 0'),
                 TEXT.replace('z > 0', 'z >= 0'))
        for text in cases:
            with self.subTest(text=text), tempfile.TemporaryDirectory() as tmp, \
                 patch('special_function_agent.real_numeric.importlib.import_module', side_effect=without_mpmath), \
                 patch('special_function_agent.real_special._run_lean') as lean:
                data = parse_identity(text)
                self.assertFalse(complete_target(data))
                self.assertFalse(has_special(data))
                data['proof'] = {'mode': 'diagnostic'}
                result = verify(data, Path(tmp)/'run', timeout=120)
                self.assertEqual(result['status'], 'needs_conditions', result)
                self.assertFalse(result['full_bessel_proof'])
                lean.assert_not_called()

    def test_coefficients_orders_numerator_and_root_cannot_be_substituted(self):
        cases = (TEXT.replace('X_02(z,lambda*z)', 'X_01(z,lambda*z)'),
                 TEXT.replace('(1/lambda)', '(2/lambda)'),
                 TEXT.replace('X_01(z,lambda*z) = 0', 'X_00(z,lambda*z) = 0'),
                 TEXT.replace('X_01(z,z)^2', 'X_01(z,lambda*z)^2'))
        for text in cases:
            with self.subTest(text=text):
                data = parse_identity(text)
                self.assertFalse(complete_target(data))
                self.assertFalse(has_special(data))
        data = request()
        numerator = data['rhs']['args'][0]['args'][1]
        data['rhs']['args'][0]['args'][1] = {'op': 'deriv', 'var': 'z', 'arg': numerator}
        self.assertIsNone(match_identity(data['lhs'], data['rhs']))

    def test_names_reverse_association_and_extra_conditions_are_preserved(self):
        data = request(TEXT.replace('lambda', 'scale').replace('z', 'radius').strip()+',radius<7', 'steps')
        self.assertEqual(data['variables'], {'radius': 'real', 'scale': 'real'})
        self.assertTrue(complete_target(data))
        data['lhs'], data['rhs'] = data['rhs'], data['lhs']
        data['proof'] = default_proof(data, 'steps')
        self.assertTrue(match_identity(data['lhs'], data['rhs'])['reverse'])
        self.assertIn('(h4 : v0 < (7 / 1 : ℝ))', render(data))
        self.assertIn(').symm', render(data))

    def test_ai_schema_rejects_target_and_analytic_premise_injection(self):
        data = request(route='steps')
        self.assertIn('cross_product_root', make_prompt(data, 'steps'))
        schema = output_schema('steps', data)
        self.assertNotIn('assumptions', schema['properties'])
        self.assertIn('cross_product_root', schema['properties']['steps']['items']['properties']['recipe']['enum'])
        for change in ('condition', 'endpoint', 'extra-target'):
            bad = deepcopy(data)
            if change == 'condition':
                bad['proof']['steps'][0]['conditions'].append('the denominator is nonzero')
            elif change == 'endpoint':
                bad['proof']['steps'][0]['after'] = {'op': 'int', 'value': 0}
            else:
                bad['proof']['lhs'] = data['lhs']
            with self.subTest(change=change), self.assertRaises(InputError):
                validate_request(bad)

    def test_legacy_diagnostic_bytes_and_new_full_scope_are_distinct(self):
        data = request(route='diagnostic')
        self.assertFalse(has_special(data))
        from special_function_agent.real_bessel import conditional_source, template_match
        self.assertEqual(conditional_source(template_match(data)),
                         (ROOT/'demo/cross-product/conditional_certificate.lean').read_text())
        with tempfile.TemporaryDirectory() as tmp, \
             patch('special_function_agent.real_numeric.importlib.import_module', side_effect=without_mpmath), \
             patch('special_function_agent.real_special._run_lean', return_value=ACCEPTED) as lean:
            output = Path(tmp)/'new'
            result = verify(request(), output, timeout=120)
            self.assertEqual(result['formal_scope'], FORMAL_SCOPE)
            self.assertTrue(result['full_bessel_proof'])
            result['formal_scope'] = 'conditional algebra'
            (output/'result.json').write_text(json.dumps(result))
            lean.reset_mock()
            with self.assertRaises(InputError):
                replay(output, timeout=120)
            lean.assert_not_called()


@unittest.skipUnless(os.environ.get('SF_RUN_LEAN_TESTS') == '1', 'Enable full cross-root Lean acceptance.')
class CrossCompleteLeanTests(unittest.TestCase):
    def test_both_routes_and_archive_replay_without_optional_backend(self):
        with tempfile.TemporaryDirectory() as tmp, \
             patch('special_function_agent.real_numeric.importlib.import_module', side_effect=without_mpmath):
            for route in ('direct', 'steps'):
                output = Path(tmp)/route
                result = verify(request(route=route), output, timeout=120)
                self.assertEqual(result['status'], 'proved', result)
                self.assertTrue(result['full_bessel_proof'])
                self.assertEqual(result['numerical']['diagnostic'], 'backend_unavailable')
                self.assertTrue(set(result['attempts'][0]['axioms']) <= ALLOWED_AXIOMS)
                self.assertTrue(replay(output, timeout=120)['replayed'])
            record = archive.register_verification(output, Path(tmp)/'archive', timeout=120)
            self.assertTrue(archive.replay_record(record['id'], Path(tmp)/'archive', timeout=120)['replayed'])

    def test_renamed_reversed_and_regrouped_rhs_preserve_the_proposition(self):
        with tempfile.TemporaryDirectory() as tmp:
            data = request(TEXT.replace('lambda', 'scale').replace('z', 'radius'), 'steps')
            numerator, denominator = data['rhs']['args']
            fraction, a = numerator['args']
            data['rhs'] = {'op': 'mul', 'args': [fraction, {'op': 'div', 'args': [a, denominator]}]}
            data['lhs'], data['rhs'] = data['rhs'], data['lhs']
            data['proof'] = default_proof(data, 'steps')
            result = verify(data, Path(tmp)/'reversed', timeout=120)
            self.assertEqual(result['status'], 'proved', result)

    def test_kernel_requires_root_and_upper_bound_for_registered_energy_proof(self):
        with tempfile.TemporaryDirectory() as tmp:
            for index in (1, 3):
                data = request()
                del data['assumptions'][index]
                source = Path(tmp)/f'missing-{index}.lean'
                source.write_text(render(data))
                self.assertFalse(_run_lean(source, timeout=120)['accepted'])


if __name__ == '__main__':
    unittest.main()
