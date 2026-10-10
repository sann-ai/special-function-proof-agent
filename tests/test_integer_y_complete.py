"""Full integer-Y recurrence, fixed-target boundaries, and legacy replay."""
from importlib import import_module
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from special_function_agent import archive
from special_function_agent.bessel_y_integer import FORMAL_SCOPE, conditional_source, match
from special_function_agent.core import ALLOWED_AXIOMS, InputError, ROOT, render_lean, replay, validate_request, verify
from special_function_agent.generate import generate, make_prompt, output_schema
from special_function_agent.parser import parse_identity
from special_function_agent.real_special import _condition, default_proof, has_special, match_identity
from special_function_agent.registry import CONVENTIONS, conventions

TEXT = 'Y_{n-1}(x)+Y_{n+1}(x)=2*n/x*Y_n(x); n integer,x>0'
ACCEPTED = {'accepted': True, 'axioms': sorted(ALLOWED_AXIOMS)}


def request(text=TEXT, route='direct'):
    target = parse_identity(text)
    return {**target, 'proof': default_proof(target, route)}


def without_mpmath(name, *args, **kwargs):
    if name == 'mpmath':
        raise ImportError('mpmath is absent in this test')
    return import_module(name, *args, **kwargs)


class IntegerYCompleteBoundaryTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.base = Path(temporary.name)
        backend = patch('special_function_agent.real_numeric.importlib.import_module', side_effect=without_mpmath)
        backend.start()
        self.addCleanup(backend.stop)
        lean = patch('special_function_agent.real_special._run_lean', return_value=ACCEPTED)
        self.lean = lean.start()
        self.addCleanup(lean.stop)

    def test_exact_examples_keep_integer_type_original_target_and_standard_definition(self):
        target = parse_identity(TEXT)
        self.assertEqual(target['variables'], {'n': 'int', 'x': 'real'})
        self.assertEqual(parse_identity((ROOT/'examples/integer-y-complete.txt').read_text()), target)
        self.assertEqual(json.loads((ROOT/'examples/integer-y-complete.target.json').read_text()), target)
        old = json.loads((ROOT/'demo/integer-y-recurrence/request.json').read_text())
        self.assertEqual(archive.target_hash(old), archive.target_hash(target))
        self.assertEqual(conventions(target), CONVENTIONS)
        for route in ('direct', 'steps'):
            data = request(route=route)
            validate_request(data)
            self.assertTrue(has_special(data))
            source = render_lean(data)
            self.assertIn('(v0 : ℤ)', source)
            self.assertIn('SpecialFunctionProofAgent.besselYInt', source)
            self.assertIn('SpecialFunctionProofAgent.besselYInt_recurrence v0 v1', source)
            self.assertNotIn('DifferentiableAt', source)
            self.assertNotIn('besselYNoninteger', source)
            self.assertEqual(data['assumptions'], target['assumptions'])

    def test_both_routes_save_full_proof_and_replay_without_numeric_backend(self):
        for route in ('direct', 'steps'):
            with self.subTest(route=route):
                output = self.base/route
                data = request(route=route)
                result = verify(data, output, timeout=120)
                self.assertEqual(result['status'], 'proved', result)
                self.assertTrue(result['full_bessel_proof'])
                self.assertTrue(result['full_function_proof'])
                self.assertEqual(result['formal_scope'], FORMAL_SCOPE)
                self.assertEqual(result['numerical']['diagnostic'], 'backend_unavailable')
                self.assertEqual(json.loads((output/'request.json').read_text()), data)
                self.assertNotIn('conditional_lean', result)
                self.assertTrue(replay(output, timeout=120)['full_bessel_proof'])
                record = archive.register_verification(output, self.base/'archive', timeout=120)
                saved = archive.replay_record(record['id'], self.base/'archive', timeout=120)
                self.assertTrue(saved['replayed'])
                self.assertTrue(saved['full_bessel_proof'])

    def test_reverse_arbitrary_name_and_extra_conditions_are_preserved(self):
        data = request(TEXT.replace('x', 'radius')+',n>=-2,radius<4', 'steps')
        data['lhs'], data['rhs'] = data['rhs'], data['lhs']
        data['proof'] = default_proof(data, 'steps')
        self.assertTrue(match_identity(data['lhs'], data['rhs'])['reverse'])
        source = render_lean(data)
        self.assertIn(').symm', source)
        self.assertIn('(v0 : ℝ) ≥ (-2 / 1 : ℝ)', source)
        result = verify(data, self.base/'reverse', timeout=120)
        self.assertEqual(result['status'], 'proved', result)
        self.assertEqual(json.loads((self.base/'reverse/request.json').read_text()), data)

    def test_wrong_coefficient_index_and_j_mixture_cannot_use_full_recipe(self):
        for mutation in ('coefficient', 'index', 'mixed'):
            data = request()
            if mutation == 'coefficient':
                data['rhs']['args'][0]['args'][0]['args'][0]['value'] = 3
            elif mutation == 'index':
                data['lhs']['args'][1]['order']['args'][1]['value'] = 2
            else:
                data['lhs']['args'][0]['op'] = 'bessel_j'
            with self.subTest(mutation=mutation):
                self.assertIsNone(match_identity(data['lhs'], data['rhs']))
                self.assertFalse(has_special(data))
                self.lean.reset_mock()
                result = verify(data, self.base/mutation, timeout=120)
                self.assertEqual(result['status'], 'unresolved', result)
                self.assertEqual(result['reason'], 'invalid_input')
                self.assertFalse((self.base/mutation/'certificate.lean').exists())
                self.lean.assert_not_called()

    def test_missing_and_nonpositive_argument_stops_before_lean(self):
        for index, condition in enumerate(('x real', 'x>=0', 'x=0', 'x<0')):
            with self.subTest(condition=condition):
                data = request(TEXT.replace('x>0', condition))
                self.lean.reset_mock()
                result = verify(data, self.base/f'domain-{index}', timeout=120)
                self.assertEqual(result['status'], 'needs_conditions', result)
                self.assertFalse(result['full_bessel_proof'])
                self.assertIn('x > 0', result['pending_domain_conditions'])
                self.assertEqual(json.loads((self.base/f'domain-{index}/request.json').read_text()), data)
                self.lean.assert_not_called()

    def test_degree_types_and_candidate_assumptions_remain_closed(self):
        with self.assertRaises(InputError):
            parse_identity(TEXT.replace('n integer', 'n natural'))
        with self.assertRaises(InputError):
            parse_identity('H_n(x)=H_n(x);n integer,x real')
        for proof in ({'mode': 'direct', 'recipe': 'integer_y_recurrence', 'assumptions': []}, [],
                      {'mode': 'steps', 'steps': []}):
            data = request()
            data['proof'] = proof
            with self.subTest(proof=proof), self.assertRaises(InputError):
                validate_request(data)
        data = request(route='steps')
        data['proof']['steps'][0]['conditions'].append('J has an order derivative')
        with self.assertRaises(InputError):
            validate_request(data)
        data = request(route='steps')
        data['proof']['steps'][0]['after'] = {'op': 'int', 'value': 0}
        with self.assertRaises(InputError):
            validate_request(data)

    def test_degree_compare_uses_the_fixed_natural_variables(self):
        for relation, symbol in (('ne', '≠'), ('lt', '<'), ('le', '≤'), ('ge', '≥')):
            self.assertEqual(_condition({'op': 'degree_compare', 'lhs': 'm',
                             'relation': relation, 'rhs': 'n'},
                             {'m': 'v0', 'n': 'v1'}, {'m': 'nat', 'n': 'nat'}), f'v0 {symbol} v1')

    def test_saved_request_source_scope_and_proof_flags_reject_tampering(self):
        for change in ('request', 'source', 'scope', 'full-proof'):
            with self.subTest(change=change):
                output = self.base/change
                result = verify(request(), output, timeout=120)
                self.assertEqual(result['status'], 'proved')
                if change == 'source':
                    path = output/'certificate.lean'
                    path.write_text(path.read_text()+'\n-- altered\n')
                elif change == 'request':
                    path = output/'request.json'
                    data = json.loads(path.read_text())
                    data['assumptions'][0]['value']['numerator'] = 1
                    path.write_text(json.dumps(data))
                else:
                    path = output/'result.json'
                    result['formal_scope' if change == 'scope' else 'full_bessel_proof'] = 'conditional' if change == 'scope' else False
                    path.write_text(json.dumps(result))
                self.lean.reset_mock()
                with self.assertRaises(InputError):
                    replay(output, timeout=120)
                self.lean.assert_not_called()

    def test_diagnostic_replay_and_other_y_cross_scopes_are_preserved(self):
        data = request(route='diagnostic')
        self.assertFalse(has_special(data))
        self.assertEqual(conditional_source(match(data)),
                         (ROOT/'demo/integer-y-recurrence/conditional_certificate.lean').read_text())
        with patch('special_function_agent.real_bessel._run_lean', return_value=ACCEPTED):
            result = verify(data, self.base/'conditional', timeout=120)
            self.assertEqual(result['status'], 'unresolved')
            self.assertFalse(result['full_bessel_proof'])
            self.assertTrue(result['conditional_lean']['accepted'])
            saved = replay(self.base/'conditional', timeout=120)
            self.assertTrue(saved['conditional_replayed'])
            self.assertFalse(saved['full_bessel_proof'])
            for index, text in enumerate(('Y_0(x)=Y_0(x);x>0',
                                         (ROOT/'examples/cross-product-root.txt').read_text())):
                target = parse_identity(text)
                diagnostic = {**target, 'proof': {'mode': 'diagnostic'}}
                self.assertFalse(has_special(diagnostic))
                result = verify(diagnostic, self.base/f'legacy-{index}', timeout=120)
                self.assertEqual(result['status'], 'unresolved')
                self.assertFalse(result['full_bessel_proof'])

    def test_ai_schema_and_prompt_support_exact_y_without_target_override(self):
        target = parse_identity(TEXT)
        self.assertIn('integer_y_recurrence', output_schema('direct', target)['properties']['recipe']['enum'])
        schema = output_schema('steps', target)
        self.assertTrue(any(s['properties']['op'].get('const') == 'bessel_y' for s in schema['$defs']['expr']['anyOf']))
        self.assertIn('order differentiability proved', make_prompt(target, 'steps'))
        for field in ('assumptions', 'lhs'):
            candidate = {**default_proof(target), field: []}
            def start(command, **kwargs):
                Path(command[command.index('--output-last-message')+1]).write_text(json.dumps(candidate))
                return SimpleNamespace(returncode=0, communicate=lambda **kw: ('', ''))
            with self.subTest(field=field), patch('special_function_agent.generate.shutil.which', return_value='/bin/codex'), \
                 patch('special_function_agent.generate.subprocess.Popen', side_effect=start), \
                 patch('special_function_agent.generate.verify') as checker:
                with self.assertRaises(InputError):
                    generate(target, 'direct', self.base/f'inject-{field}', attempts=1)
                checker.assert_not_called()


@unittest.skipUnless(os.environ.get('SF_RUN_LEAN_TESTS') == '1', 'Enable full integer-Y Lean acceptance.')
class IntegerYCompleteLeanTests(unittest.TestCase):
    def test_direct_steps_cli_and_replay_without_optional_backend(self):
        for route in ('direct', 'steps'):
            with self.subTest(route=route), tempfile.TemporaryDirectory() as directory, \
                 patch('special_function_agent.real_numeric.importlib.import_module', side_effect=without_mpmath):
                output = Path(directory)/'run'
                data = request(route=route)
                result = verify(data, output, timeout=120)
                self.assertEqual(result['status'], 'proved', result)
                self.assertTrue(result['full_bessel_proof'])
                self.assertEqual(result['numerical']['diagnostic'], 'backend_unavailable')
                self.assertTrue(set(result['attempts'][0]['axioms']) <= ALLOWED_AXIOMS)
                self.assertTrue(replay(output, timeout=120)['full_bessel_proof'])
                if route == 'steps':
                    record = archive.register_verification(output, Path(directory)/'archive', timeout=120)
                    self.assertTrue(archive.replay_record(record['id'], Path(directory)/'archive', timeout=120)['replayed'])
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)/'cli'
            commands = ([sys.executable, '-m', 'special_function_agent', 'verify',
                         'examples/integer-y-complete.txt', '--route', 'direct', '--output', str(output), '--timeout', '120'],
                        [sys.executable, '-m', 'special_function_agent', 'replay', str(output), '--timeout', '120'])
            for command in commands:
                p = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=150)
                self.assertEqual(p.returncode, 0, p.stdout+p.stderr)
                self.assertTrue(json.loads(p.stdout)['full_bessel_proof'])

    def test_reverse_named_argument_and_legacy_conditional_replay(self):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            data = request(TEXT.replace('x', 'radius')+',n>=-2,radius<4', 'steps')
            data['lhs'], data['rhs'] = data['rhs'], data['lhs']
            data['proof'] = default_proof(data, 'steps')
            result = verify(data, base/'reverse', timeout=120)
            self.assertEqual(result['status'], 'proved', result)
            self.assertTrue(replay(base/'reverse', timeout=120)['full_bessel_proof'])
            result = verify(request(route='diagnostic'), base/'legacy', timeout=120)
            self.assertEqual(result['status'], 'unresolved', result)
            self.assertFalse(result['full_bessel_proof'])
            self.assertTrue(result['conditional_lean']['accepted'])
            saved = replay(base/'legacy', timeout=120)
            self.assertTrue(saved['conditional_replayed'])
            self.assertFalse(saved['replayed'])


if __name__ == '__main__':
    unittest.main()
