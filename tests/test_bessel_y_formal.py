"""Standard noninteger Y certificates and the unchanged legacy diagnostic scope."""
import copy
import importlib.util
import json
import os
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from special_function_agent import archive
from special_function_agent.core import (
    ALLOWED_AXIOMS, InputError, NeedsConditions, ROOT, render_lean, replay,
    validate_request, verify,
)
from special_function_agent.generate import generate
from special_function_agent.parser import parse_identity
from special_function_agent.real_numeric import diagnose
from special_function_agent.real_special import default_proof, has_special, match_identity


RECURRENCE = ('YNoninteger(-1/2,x)+YNoninteger(3/2,x)='
              'YNoninteger(1/2,x)/x; x>0')
DERIVATIVE = ('D_x(YNoninteger(1/2,x))='
              '(YNoninteger(-1/2,x)-YNoninteger(3/2,x))/2; x>0')
ACCEPTED = {'accepted': True, 'axioms': sorted(ALLOWED_AXIOMS)}


def request(text=RECURRENCE, route='direct'):
    target = parse_identity(text)
    return {**target, 'proof': default_proof(target, route)}


class BesselYFormalBoundaryTests(unittest.TestCase):
    def test_explicit_noninteger_name_preserves_exact_orders_and_formal_definition(self):
        for text, theorem in ((RECURRENCE, 'Yhalf_recurrence'), (DERIVATIVE, 'Yhalf_derivative')):
            with self.subTest(theorem=theorem):
                data = request(text)
                validate_request(data)
                self.assertTrue(has_special(data))
                self.assertIsNotNone(match_identity(data['lhs'], data['rhs']))
                source = render_lean(data)
                self.assertIn('SpecialFunctionProofAgent.'+theorem, source)
                self.assertIn('SpecialFunctionProofAgent.besselYNoninteger', source)
                self.assertIn('(h0 : v0 > (0 / 1 : ℝ))', source)
                self.assertNotIn('DifferentiableAt', source)
                self.assertNotIn('besselYInt', source)
        target = parse_identity(RECURRENCE)
        first, second = target['lhs']['args']
        self.assertEqual(first['op'], 'bessel_y_noninteger')
        self.assertEqual(first['order'], {'op': 'rational', 'numerator': -1, 'denominator': 2})
        self.assertEqual(second['order'], {'op': 'rational', 'numerator': 3, 'denominator': 2})
        self.assertEqual(target['variables'], {'x': 'real'})
        legacy = parse_identity(RECURRENCE.replace('YNoninteger', 'Y'))
        self.assertNotEqual(archive.target_hash(target), archive.target_hash(legacy))
        self.assertFalse(has_special(legacy))

    def test_wrong_coefficients_and_supported_but_wrong_orders_fail_recipe_matching(self):
        for text in (RECURRENCE, DERIVATIVE):
            for mutation in ('coefficient', 'order'):
                data = request(text)
                if mutation == 'coefficient':
                    data['rhs'] = {'op': 'mul', 'args': [{'op': 'int', 'value': 2}, data['rhs']]}
                else:
                    node = data['lhs']['args'][0] if text == RECURRENCE else data['lhs']['arg']
                    node['order'] = {'op': 'rational', 'numerator': 3, 'denominator': 2}
                with self.subTest(text=text, mutation=mutation):
                    self.assertIsNone(match_identity(data['lhs'], data['rhs']))
                    with self.assertRaises(InputError):
                        render_lean(data)

    def test_integer_variable_and_out_of_scope_orders_are_rejected(self):
        for order, conditions in (('0', 'x>0'), ('1', 'x>0'), ('5/2', 'x>0'),
                                  ('n', 'n integer,x>0'), ('n', 'n natural,x>0')):
            with self.subTest(order=order, conditions=conditions), self.assertRaises(InputError):
                parse_identity(f'YNoninteger({order},x)=YNoninteger({order},x); {conditions}')

    def test_missing_or_nonpositive_domains_stop_before_lean(self):
        for condition in ('x real', 'x>=0', 'x=0', 'x<0', 'x=-1'):
            for text in (RECURRENCE, DERIVATIVE):
                with self.subTest(condition=condition, text=text), tempfile.TemporaryDirectory() as directory, \
                     patch('special_function_agent.real_numeric.diagnose', return_value={'diagnostic': 'backend_unavailable'}), \
                     patch('special_function_agent.real_special._run_lean') as lean:
                    result = verify(request(text.replace('x>0', condition)), Path(directory)/'run')
                    self.assertEqual(result['status'], 'needs_conditions', result)
                    self.assertFalse(result.get('full_function_proof', False))
                    self.assertFalse(result.get('full_bessel_proof', False))
                    lean.assert_not_called()

    def test_step_endpoints_and_injected_target_assumptions_are_closed(self):
        original = request(DERIVATIVE, 'steps')
        for mutation in ('before', 'after', 'conditions', 'assumptions', 'lhs'):
            changed = copy.deepcopy(original)
            step = changed['proof']['steps'][0]
            if mutation in {'before', 'after'}:
                step[mutation] = {'op': 'int', 'value': 0}
            elif mutation == 'conditions':
                step['conditions'].append('YNoninteger(1/2,x)=0')
            else:
                changed['proof'][mutation] = []
            with self.subTest(mutation=mutation), self.assertRaises(InputError):
                validate_request(changed)
        with self.assertRaises(NeedsConditions):
            parse_identity('YNoninteger(1/2,x)=0; x>0,YNoninteger(1/2,x)=0')

    def test_ai_cannot_replace_target_or_add_assumptions(self):
        target = parse_identity(RECURRENCE)
        for field, value in (('assumptions', []), ('lhs', {'op': 'int', 'value': 0})):
            candidate = {**default_proof(target), field: value}

            def start(command, **kwargs):
                Path(command[command.index('--output-last-message')+1]).write_text(json.dumps(candidate))
                return SimpleNamespace(returncode=0, communicate=lambda **kw: ('', ''))

            with self.subTest(field=field), tempfile.TemporaryDirectory() as directory, \
                 patch('special_function_agent.generate.shutil.which', return_value='/bin/codex'), \
                 patch('special_function_agent.generate.subprocess.Popen', side_effect=start), \
                 patch('special_function_agent.generate.verify') as checker:
                with self.assertRaises(InputError):
                    generate(target, 'direct', Path(directory)/'run', attempts=1)
                checker.assert_not_called()

    def test_replay_rejects_modified_saved_evidence_before_lean(self):
        for mutation in ('request', 'certificate', 'conventions', 'scope'):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory, \
                 patch('special_function_agent.real_numeric.diagnose', return_value={'diagnostic': 'backend_unavailable'}):
                output = Path(directory)/'run'
                with patch('special_function_agent.real_special._run_lean', return_value=ACCEPTED):
                    result = verify(request(), output)
                    self.assertEqual(result['status'], 'proved')
                if mutation == 'certificate':
                    path = output/'certificate.lean'
                    path.write_text(path.read_text()+'\n-- altered evidence\n')
                else:
                    path = output/('request.json' if mutation == 'request' else 'result.json')
                    saved = json.loads(path.read_text())
                    if mutation == 'request':
                        saved['assumptions'][0]['value']['numerator'] = 1
                    elif mutation == 'scope':
                        saved['formal_scope'] = 'all integer orders'
                    else:
                        saved['conventions'] = {}
                    path.write_text(json.dumps(saved))
                with patch('special_function_agent.real_special._run_lean') as lean:
                    with self.assertRaises(InputError):
                        replay(output, timeout=120)
                    lean.assert_not_called()

    def test_legacy_y_and_cross_root_keep_diagnostic_scope_and_all_conditions(self):
        texts = ['Y_0(x)=Y_0(x); x>0', RECURRENCE.replace('YNoninteger', 'Y'),
                 'YNoninteger(1/2,x)=Y(1/2,x); x>0',
                 (ROOT/'examples/cross-product-root.txt').read_text()]
        for text in texts:
            data = {**parse_identity(text), 'proof': {'mode': 'diagnostic'}}
            with self.subTest(text=text), tempfile.TemporaryDirectory() as directory, \
                 patch('special_function_agent.real_bessel._run_lean', return_value=ACCEPTED), \
                 patch('special_function_agent.real_numeric.importlib.import_module', side_effect=ImportError):
                output = Path(directory)/'run'
                result = verify(data, output, timeout=120)
                self.assertEqual(result['status'], 'unresolved', result)
                self.assertFalse(result['full_bessel_proof'])
                self.assertEqual(json.loads((output/'request.json').read_text()), data)
                self.assertFalse((output/'certificate.lean').exists())
                if 'X_00' in text:
                    self.assertEqual(len(data['assumptions']), 4)
                    self.assertTrue(result['conditional_lean']['accepted'])


@unittest.skipUnless(importlib.util.find_spec('mpmath'), 'uses the existing mpmath runtime')
class BesselYFormalNumericalTests(unittest.TestCase):
    def test_half_integer_formulas_and_wrong_coefficient(self):
        for text in (RECURRENCE, DERIVATIVE):
            with self.subTest(text=text):
                result = diagnose(parse_identity(text))
                self.assertEqual(result['diagnostic'], 'no_mismatch_found', result)
                self.assertGreater(result['checked_samples'], 0)
                self.assertFalse(result['full_function_proof'])
        bad = RECURRENCE.replace('=YNoninteger', '=2*YNoninteger')
        self.assertEqual(diagnose(parse_identity(bad))['diagnostic'], 'counterexample_candidates')


@unittest.skipUnless(os.environ.get('SF_RUN_LEAN_TESTS') == '1', 'Enable real Bessel Y Lean acceptance.')
class BesselYFormalLeanTests(unittest.TestCase):
    def test_both_formulas_direct_steps_and_replay(self):
        for text in (RECURRENCE, DERIVATIVE):
            for route in ('direct', 'steps'):
                with self.subTest(text=text, route=route), tempfile.TemporaryDirectory() as directory, \
                     patch('special_function_agent.real_numeric.diagnose', return_value={'diagnostic': 'backend_unavailable'}):
                    data = request(text, route)
                    output = Path(directory)/'run'
                    result = verify(data, output, timeout=120)
                    self.assertEqual(result['status'], 'proved', result)
                    self.assertTrue(result['full_function_proof'])
                    self.assertTrue(result['full_bessel_proof'])
                    self.assertTrue(set(result['attempts'][-1]['axioms']) <= ALLOWED_AXIOMS)
                    self.assertTrue((output/'certificate.lean').is_file())
                    self.assertEqual(json.loads((output/'request.json').read_text()), data)
                    replayed = replay(output, timeout=120)
                    self.assertTrue(replayed['replayed'])
                    self.assertTrue(replayed['full_bessel_proof'])

    def test_formal_archive_and_replay_continue_without_mpmath(self):
        with tempfile.TemporaryDirectory() as directory, \
             patch('special_function_agent.real_numeric.importlib.import_module', side_effect=ImportError):
            base = Path(directory)
            result = verify(request(DERIVATIVE, 'steps'), base/'run', timeout=120)
            self.assertEqual(result['status'], 'proved', result)
            self.assertEqual(result['numerical']['diagnostic'], 'backend_unavailable')
            record = archive.register_verification(base/'run', base/'archive', timeout=120)
            self.assertEqual(record['status'], 'proved')
            self.assertEqual(record['request'], request(DERIVATIVE, 'steps'))
            self.assertTrue(archive.replay_record(record['id'], base/'archive', timeout=120)['replayed'])

    def test_false_coefficient_and_order_remain_unresolved(self):
        texts = [RECURRENCE.replace('=YNoninteger', '=2*YNoninteger'),
                 DERIVATIVE.replace('D_x(YNoninteger(1/2,x))', 'D_x(YNoninteger(3/2,x))')]
        for text in texts:
            with self.subTest(text=text), tempfile.TemporaryDirectory() as directory, \
                 patch('special_function_agent.real_numeric.diagnose', return_value={'diagnostic': 'backend_unavailable'}):
                output = Path(directory)/'run'
                result = verify(request(text), output, timeout=120)
                self.assertEqual(result['status'], 'unresolved', result)
                self.assertFalse(result.get('full_function_proof', False))
                self.assertFalse(result.get('full_bessel_proof', False))
                self.assertFalse((output/'certificate.lean').exists())


if __name__ == '__main__':
    unittest.main()
