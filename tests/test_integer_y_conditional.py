"""Integer-Y analytic premises stay visible and separate from the full target."""
import hashlib
import html
from importlib import import_module
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from special_function_agent import archive
from special_function_agent.core import ALLOWED_AXIOMS, InputError, ROOT, replay, validate_request, verify
from special_function_agent.generate import generate
from special_function_agent.parser import parse_identity
from special_function_agent.real_bessel import template_match
from special_function_agent.real_special import default_proof


TEXT = 'Y_{n-1}(x)+Y_{n+1}(x)=2*n/x*Y_n(x); n integer,x>0'
PREMISES = ['0 < x',
            'DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 0',
            'DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 1']
ACCEPTED = {'accepted': True, 'axioms': sorted(ALLOWED_AXIOMS)}


def request(text=TEXT):
    return {**parse_identity(text), 'proof': {'mode': 'diagnostic'}}


def without_mpmath(name, *args, **kwargs):
    if name == 'mpmath':
        raise ImportError('mpmath is absent in this test')
    return import_module(name, *args, **kwargs)


class IntegerYConditionalBoundaryTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.base = Path(temporary.name)
        backend = patch('special_function_agent.real_numeric.importlib.import_module', side_effect=without_mpmath)
        backend.start()
        self.addCleanup(backend.stop)
        lean = patch('special_function_agent.real_bessel._run_lean', return_value=ACCEPTED)
        self.lean = lean.start()
        self.addCleanup(lean.stop)

    def checked(self, data=None, name='run'):
        data = request() if data is None else data
        output = self.base/name
        result = verify(data, output, timeout=120)
        return output, result

    def assert_conditional(self, result):
        self.assertEqual(result['status'], 'unresolved', result)
        self.assertFalse(result['full_bessel_proof'])
        self.assertTrue(result['conditional_lean']['accepted'])

    def test_published_target_and_every_saved_premise_remain_explicit(self):
        target = parse_identity(TEXT)
        self.assertEqual(parse_identity((ROOT/'examples/integer-y-recurrence.txt').read_text()), target)
        self.assertEqual(json.loads((ROOT/'examples/integer-y-recurrence.target.json').read_text()), target)
        data = request(TEXT+',n>=1,x<4')
        output, result = self.checked(data)
        self.assert_conditional(result)
        self.assertEqual(result['analysis']['assumptions'], PREMISES)
        self.assertEqual(result['conditional_lean']['assumptions'], PREMISES)
        self.assertEqual(len(result['analysis']['formal_obligations']), 2)
        self.assertEqual(json.loads((output/'analysis.json').read_text()), result['analysis'])
        self.assertEqual(json.loads((output/'request.json').read_text()), data)
        self.assertEqual(len(data['assumptions']), 3)
        self.assertEqual(data['variables'], {'n': 'int', 'x': 'real'})
        self.assertFalse((output/'certificate.lean').exists())
        source = (output/'conditional_certificate.lean').read_text()
        self.assertIn('besselYInt_recurrence_of_order_differentiable_zero_one n x hx h0 h1', source)
        for index in (0, 1):
            self.assertIn(f'(h{index} : DifferentiableAt ℝ', source)
            self.assertIn(f'realBesselJ a x) {index})', source)
            self.assertIn(PREMISES[index+1], (output/'report.md').read_text())
        replayed = replay(output, timeout=120)
        self.assertTrue(replayed['conditional_replayed'])
        self.assertFalse(replayed['replayed'])
        self.assertFalse(replayed['full_bessel_proof'])

    def test_reverse_and_arbitrary_real_name_keep_the_substitution(self):
        for reverse in (False, True):
            data = request(TEXT.replace('x', 'radius'))
            if reverse:
                data['lhs'], data['rhs'] = data['rhs'], data['lhs']
            output, result = self.checked(data, f'renamed-{reverse}')
            self.assert_conditional(result)
            self.assertEqual(result['analysis']['substitutions'], {'n': 'n', 'x': 'radius'})
            self.assertEqual(result['analysis']['reverse'], reverse)
            self.assertEqual(result['conditional_lean']['assumptions'], PREMISES)
            source = (output/'conditional_certificate.lean').read_text()
            self.assertEqual(').symm' in source, reverse)
            self.assertEqual(json.loads((output/'request.json').read_text()), data)
            self.assertTrue(replay(output, timeout=120)['conditional_replayed'])

    def test_wrong_coefficient_index_and_mixed_j_y_have_no_template(self):
        for name in ('coefficient', 'index', 'mixed'):
            data = request()
            if name == 'coefficient':
                data['rhs']['args'][0]['args'][0]['args'][0]['value'] = 3
            elif name == 'index':
                data['lhs']['args'][1]['order']['args'][1]['value'] = 2
            else:
                data['lhs']['args'][0]['op'] = 'bessel_j'
            with self.subTest(mutation=name):
                self.assertIsNone(template_match(data))
                self.lean.reset_mock()
                output, result = self.checked(data, name)
                self.assertEqual(result['status'], 'unresolved')
                self.assertFalse(result['full_bessel_proof'])
                self.assertFalse(result['conditional_lean']['accepted'])
                self.assertFalse((output/'conditional_certificate.lean').exists())
                self.lean.assert_not_called()

    def test_missing_or_nonpositive_argument_never_strengthens_input(self):
        for index, condition in enumerate(('x real', 'x>=0', 'x=0', 'x<0')):
            data = request(TEXT.replace('x>0', condition))
            with self.subTest(condition=condition):
                output, result = self.checked(data, f'domain-{index}')
                self.assertEqual(result['status'], 'needs_conditions', result)
                self.assertIn('x > 0', result['pending_domain_conditions'])
                self.assertFalse(result['full_bessel_proof'])
                self.assertEqual(json.loads((output/'request.json').read_text()), data)
                self.assertFalse((output/'certificate.lean').exists())

    def test_natural_degree_or_candidate_premise_injection_is_rejected(self):
        with self.assertRaises(InputError):
            parse_identity(TEXT.replace('n integer', 'n natural'))
        candidates = [dict(mode='direct', recipe='integer_y_recurrence', assumptions=PREMISES),
                      dict(mode='steps', steps=[]),
                      dict(mode='diagnostic', assumptions=PREMISES),
                      dict(mode='diagnostic', h0=True, h1=True)]
        for index, candidate in enumerate(candidates):
            data = request()
            data['proof'] = candidate
            with self.subTest(candidate=candidate):
                with self.assertRaises(InputError):
                    validate_request(data)
                self.lean.reset_mock()
                _, result = self.checked(data, f'injected-{index}')
                self.assertEqual(result['status'], 'unresolved')
                self.assertEqual(result['reason'], 'invalid_input')
                self.assertFalse(result.get('full_bessel_proof', False))
                self.lean.assert_not_called()
        data = request()
        data['assumptions'].append({'op': 'DifferentiableAt', 'order': 0})
        with self.assertRaises(InputError):
            validate_request(data)

    def test_saved_scope_analysis_premises_and_status_tampering_is_rejected(self):
        for mutation in ('analysis', 'scope', 'remove-h0', 'remove-h1', 'replace-h0',
                         'replace-h1', 'status', 'full-proof'):
            with self.subTest(mutation=mutation):
                output, _ = self.checked(name=mutation)
                path = output/'result.json'
                result = json.loads(path.read_text())
                if mutation == 'analysis':
                    result['analysis']['formal_obligations'] = []
                elif mutation == 'scope':
                    result['conditional_lean']['scope'] = 'full_integer_y'
                elif mutation in ('status', 'full-proof'):
                    result['status' if mutation == 'status' else 'full_bessel_proof'] = 'proved' if mutation == 'status' else True
                else:
                    index = int(mutation[-1])+1
                    if mutation.startswith('remove'):
                        result['conditional_lean']['assumptions'].pop(index)
                    else:
                        result['conditional_lean']['assumptions'][index] = 'True'
                path.write_text(json.dumps(result))
                self.lean.reset_mock()
                with self.assertRaises(InputError):
                    replay(output, timeout=120)
                self.lean.assert_not_called()

    def test_analysis_sidecar_premise_tampering_is_rejected(self):
        output, _ = self.checked()
        path = output/'analysis.json'
        analysis = json.loads(path.read_text())
        analysis['assumptions'] = []
        path.write_text(json.dumps(analysis))
        self.lean.reset_mock()
        with self.assertRaises(InputError):
            replay(output, timeout=120)
        self.lean.assert_not_called()

    def test_source_premise_removal_or_replacement_rejects_even_updated_hash(self):
        for index in (0, 1):
            for change in ('remove', 'replace'):
                with self.subTest(premise=index, change=change):
                    output, _ = self.checked(name=f'source-{index}-{change}')
                    path = output/'conditional_certificate.lean'
                    source = path.read_text()
                    line = next(line for line in source.splitlines() if f'(h{index} : DifferentiableAt' in line)
                    source = source.replace(line, '' if change == 'remove' else f'    (h{index} : True)'+(' :' if index == 1 else ''))
                    path.write_text(source)
                    result_path = output/'result.json'
                    result = json.loads(result_path.read_text())
                    result['conditional_lean']['sha256'] = hashlib.sha256(source.encode()).hexdigest()
                    result_path.write_text(json.dumps(result))
                    self.lean.reset_mock()
                    with self.assertRaises(InputError):
                        replay(output, timeout=120)
                    self.lean.assert_not_called()

    def test_optional_backend_archive_preserves_premises_and_replays_conditionally(self):
        data = request()
        output, result = self.checked(data)
        self.assertEqual(result['numerical']['diagnostic'], 'backend_unavailable')
        self.lean.reset_mock()
        record = archive.register_verification(output, self.base/'archive', timeout=120)
        self.lean.assert_called_once()
        self.assertEqual(record['status'], 'unresolved')
        self.assertEqual(record['request'], data)
        entry = Path(record['verification_dir']).parent
        detail = html.unescape((entry/'detail.md').read_text())
        for premise in PREMISES:
            self.assertIn(premise, detail)
        for obligation in result['analysis']['formal_obligations']:
            self.assertIn(obligation, detail)
        replayed = archive.replay_record(record['id'], self.base/'archive', timeout=120)
        self.assertTrue(replayed['conditional_replayed'])
        self.assertFalse(replayed['replayed'])
        self.assertFalse(replayed['full_bessel_proof'])

    def test_archive_rejects_altered_premises_before_registration(self):
        output, _ = self.checked()
        path = output/'result.json'
        result = json.loads(path.read_text())
        result['conditional_lean']['assumptions'].pop()
        path.write_text(json.dumps(result))
        self.lean.reset_mock()
        with self.assertRaises(InputError):
            archive.register_verification(output, self.base/'archive', timeout=120)
        self.lean.assert_not_called()
        self.assertEqual(archive.list_records(self.base/'archive'), [])

    def test_registered_evidence_and_manifest_tampering_are_rejected(self):
        for mutation in ('evidence', 'manifest'):
            with self.subTest(mutation=mutation):
                output, _ = self.checked(name=mutation)
                archive_root = self.base/f'archive-{mutation}'
                record = archive.register_verification(output, archive_root, timeout=120)
                verification = Path(record['verification_dir'])
                if mutation == 'evidence':
                    path = verification/'analysis.json'
                    analysis = json.loads(path.read_text())
                    analysis['assumptions'] = []
                    path.write_text(json.dumps(analysis))
                else:
                    path = verification.parent/'manifest.json'
                    manifest = json.loads(path.read_text())
                    manifest['files']['verification/result.json'] = '0'*64
                    path.write_text(json.dumps(manifest))
                self.lean.reset_mock()
                with self.assertRaises(InputError):
                    archive.replay_record(record['id'], archive_root, timeout=120)
                self.lean.assert_not_called()

    def test_failed_conditional_compilation_does_not_promote_target(self):
        self.lean.return_value = {'accepted': False, 'reason': 'compile_failed'}
        output, result = self.checked()
        self.assertEqual(result['status'], 'unresolved')
        self.assertFalse(result['full_bessel_proof'])
        self.assertFalse(result['conditional_lean']['accepted'])
        self.assertFalse((output/'certificate.lean').exists())

    def test_unresolved_cross_generator_routes_keep_diagnostics_and_skip_ai(self):
        # The original root identity now has a full recipe. This altered
        # coefficient remains outside that closed mathematical scope.
        text = (ROOT/'examples/cross-product-root.txt').read_text().replace('(1/lambda)', '(2/lambda)')
        for route in ('direct', 'steps'):
            with self.subTest(route=route), patch('special_function_agent.generate.subprocess.Popen') as process:
                result = generate(parse_identity(text), route, self.base/f'generated-{route}')
                process.assert_not_called()
                self.assertNotEqual(result['status'], 'proved')
                self.assertFalse(result['full_bessel_proof'])
                self.assertFalse(result['generation']['ai_called'])

    def test_legacy_cross_and_explicit_noninteger_y_keep_their_states(self):
        cross = request((ROOT/'examples/cross-product-root.txt').read_text())
        _, result = self.checked(cross, 'cross')
        self.assert_conditional(result)
        self.assertEqual(result['analysis']['id'], 'cross_product_root_fraction')
        self.assertEqual(len(cross['assumptions']), 4)
        _, legacy = self.checked(request('Y_0(x)=Y_0(x);x>0'), 'legacy')
        self.assertEqual(legacy['status'], 'unresolved')
        self.assertFalse(legacy['full_bessel_proof'])
        half = parse_identity((ROOT/'examples/yhalf-recurrence.txt').read_text())
        half['proof'] = default_proof(half, 'steps')
        with patch('special_function_agent.real_special._run_lean', return_value=ACCEPTED):
            _, result = self.checked(half, 'half')
        self.assertEqual(result['status'], 'proved')
        self.assertTrue(result['full_bessel_proof'])


@unittest.skipUnless(os.environ.get('SF_RUN_LEAN_TESTS') == '1', 'Enable integer-Y conditional Lean acceptance.')
class IntegerYConditionalLeanTests(unittest.TestCase):
    def test_forward_reverse_and_archive_replay_without_numeric_backend(self):
        for reverse in (False, True):
            with self.subTest(reverse=reverse), tempfile.TemporaryDirectory() as directory, \
                 patch('special_function_agent.real_numeric.importlib.import_module', side_effect=without_mpmath):
                base = Path(directory)
                data = request(TEXT.replace('x', 'radius'))
                if reverse:
                    data['lhs'], data['rhs'] = data['rhs'], data['lhs']
                result = verify(data, base/'run', timeout=120)
                self.assertEqual(result['status'], 'unresolved', result)
                self.assertFalse(result['full_bessel_proof'])
                self.assertTrue(result['conditional_lean']['accepted'], result)
                self.assertTrue(set(result['conditional_lean']['axioms']) <= ALLOWED_AXIOMS)
                self.assertEqual(result['numerical']['diagnostic'], 'backend_unavailable')
                replayed = replay(base/'run', timeout=120)
                self.assertTrue(replayed['conditional_replayed'])
                self.assertFalse(replayed['replayed'])
                self.assertFalse(replayed['full_bessel_proof'])
                if not reverse:
                    record = archive.register_verification(base/'run', base/'archive', timeout=120)
                    saved = archive.replay_record(record['id'], base/'archive', timeout=120)
                    self.assertTrue(saved['conditional_replayed'])
                    self.assertFalse(saved['full_bessel_proof'])

    def test_cli_reports_unresolved_exit_one_for_verification_and_replay(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)/'run'
            commands = ([sys.executable, '-m', 'special_function_agent', 'verify',
                         str(ROOT/'examples/integer-y-recurrence.txt'), '--route', 'diagnostic', '--output', str(output), '--timeout', '120'],
                        [sys.executable, '-m', 'special_function_agent', 'replay', str(output), '--timeout', '120'])
            for index, command in enumerate(commands):
                result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=150)
                self.assertEqual(result.returncode, 1, result.stderr)
                data = json.loads(result.stdout)
                self.assertEqual(data['status'], 'unresolved', data)
                self.assertFalse(data['full_bessel_proof'])
                if index:
                    self.assertTrue(data['conditional_replayed'])
                    self.assertFalse(data['replayed'])
                else:
                    self.assertTrue(data['conditional_lean']['accepted'])


if __name__ == '__main__':
    unittest.main()
