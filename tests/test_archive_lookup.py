"""Exact, route-specific proof lookup is read-only and never invokes generation."""
from contextlib import redirect_stdout
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from special_function_agent import archive
from special_function_agent.__main__ import main
from special_function_agent.core import InputError, ROOT, load_json, verify
from special_function_agent.parser import parse_identity
from special_function_agent.real_special import default_proof


ACCEPTED = {'accepted': True, 'axioms': ['Classical.choice', 'Quot.sound', 'propext']}
GAMMA = 'Gamma(x+1)=x*Gamma(x)'


def target(conditions='x>0'):
    return parse_identity(GAMMA, conditions)


def snapshot(root):
    return {path.relative_to(root).as_posix(): (path.read_bytes(), path.stat().st_mtime_ns)
            for path in root.rglob('*') if path.is_file()}


def store(base, route='direct', name='run'):
    data = target()
    request = {**data, 'proof': default_proof(data, route)}
    with patch('special_function_agent.real_special._run_lean', return_value=ACCEPTED), \
            patch('special_function_agent.real_numeric.importlib.import_module', side_effect=ImportError):
        result = verify(request, base/name)
        assert result['status'] == 'proved'
        return archive.register_verification(base/name, base/'archive')


def rehash(entry):
    manifest = load_json(entry/'manifest.json')
    manifest['files'] = {name: hashlib.sha256((entry/name).read_bytes()).hexdigest()
                         for name in manifest['files']}
    (entry/'manifest.json').write_text(json.dumps(manifest))


def cli(arguments):
    output = io.StringIO()
    with patch.object(sys, 'argv', ['special_function_agent', *map(str, arguments)]), redirect_stdout(output):
        code = main()
    return code, json.loads(output.getvalue())


class ArchiveLookupTests(unittest.TestCase):
    def test_exact_success_replays_only_chosen_route_and_preserves_all_bytes(self):
        with tempfile.TemporaryDirectory() as folder:
            base = Path(folder)
            direct = store(base)
            steps = store(base, 'steps', 'steps-run')
            root = base/'archive'
            (root/'index.json').write_text('stale index must remain untouched')
            before = snapshot(root)
            with patch('special_function_agent.real_special._run_lean', return_value=ACCEPTED) as lean, \
                    patch('special_function_agent.archive._index', side_effect=AssertionError('lookup wrote index')):
                result = archive.lookup({**target(), 'proof': {'mode': 'steps'}}, 'direct', root, timeout=17)
            self.assertEqual(result['status'], 'proved')
            self.assertTrue(result['replayed'])
            self.assertFalse(result['ai_called'])
            self.assertEqual(result['reused_record_id'], direct['id'])
            self.assertEqual(result['certificate_dir'], direct['verification_dir'])
            self.assertEqual(result['target_sha256'], archive.target_hash(target()))
            self.assertIn({'record_id': steps['id'], 'reason': 'route_mismatch'}, result['skipped'])
            self.assertEqual(lean.call_count, 1)
            self.assertEqual(lean.call_args.args, (Path(direct['verification_dir'])/'certificate.lean', 17))
            self.assertEqual(snapshot(root), before)

    def test_names_types_all_conditions_orientation_and_route_are_fixed(self):
        with tempfile.TemporaryDirectory() as folder:
            base = Path(folder)
            store(base)
            original = target()
            renamed = parse_identity(GAMMA.replace('x', 'z'), 'z>0')
            swapped = {**original, 'lhs': original['rhs'], 'rhs': original['lhs']}
            queries = [target('x>1'), target('x>0,x!=2'), renamed, swapped,
                       {**original, 'variables': {'x': 'real', 'n': 'int'}},
                       {**original, 'variables': {'x': 'real', 'n': 'nat'}}]
            self.assertNotEqual(archive.target_hash(queries[-2]), archive.target_hash(queries[-1]))
            before = snapshot(base/'archive')
            with patch('special_function_agent.archive.replay_record') as replay:
                for query in queries:
                    with self.subTest(query=query):
                        self.assertEqual(archive.lookup(query, 'direct', base/'archive')['status'], 'not_found')
                mismatch = archive.lookup(original, 'steps', base/'archive')
                self.assertEqual(mismatch['status'], 'not_found')
                self.assertEqual(mismatch['skipped'][0]['reason'], 'route_mismatch')
                with self.assertRaises(InputError):
                    archive.lookup({**original, 'variables': {'x': 'nat'}}, 'direct', base/'archive')
                replay.assert_not_called()
            self.assertEqual(snapshot(base/'archive'), before)

    def test_missing_archive_and_not_found_cli_create_no_output(self):
        with tempfile.TemporaryDirectory() as folder:
            base = Path(folder)
            source = base/'input.json'
            source.write_text(json.dumps(target()))
            missing = base/'missing'
            code, result = cli(['archive', 'lookup', source, '--route', 'steps', '--archive-dir', missing])
            self.assertEqual((code, result['status'], result['ai_called']), (1, 'not_found', False))
            self.assertEqual(result['skipped'], [])
            self.assertFalse(missing.exists())
            self.assertEqual(set(base.iterdir()), {source})

    def test_cli_json_proof_and_text_conditions_preserve_fixed_target_without_generation(self):
        with tempfile.TemporaryDirectory() as folder:
            base = Path(folder)
            record = store(base, 'steps')
            source = base/'input.json'
            # A lookup uses only the fixed theorem; the supplied candidate is never run.
            source.write_text(json.dumps({**target(), 'proof': {'mode': 'direct', 'recipe': 'unused-candidate'}}))
            text = base/'input.txt'
            text.write_text(GAMMA)
            before = snapshot(base/'archive')
            with patch('special_function_agent.real_special._run_lean', return_value=ACCEPTED), \
                    patch('subprocess.run', side_effect=AssertionError('Unexpected external generator')):
                for input_path, extra in ((source, []), (text, ['--conditions', 'x>0'])):
                    with self.subTest(input=input_path):
                        code, result = cli(['archive', 'lookup', input_path, '--route', 'steps',
                                            '--archive-dir', base/'archive', '--timeout', '17', *extra])
                        self.assertEqual(code, 0)
                        self.assertEqual(result['reused_record_id'], record['id'])
                        self.assertFalse(result['ai_called'])
            code, invalid = cli(['archive', 'lookup', source, '--route', 'steps', '--conditions', 'x>1',
                                  '--archive-dir', base/'archive'])
            self.assertEqual(code, 2)
            self.assertFalse(invalid['ai_called'])
            self.assertIn('fixed', invalid['detail'])
            self.assertEqual(snapshot(base/'archive'), before)

    def test_corrupt_new_record_is_skipped_and_older_valid_evidence_remains_usable(self):
        with tempfile.TemporaryDirectory() as folder:
            base = Path(folder)
            older = store(base, name='old')
            newer = store(base, name='new')
            (Path(newer['verification_dir'])/'certificate.lean').write_text('axiom injected : False\n')
            before = snapshot(base/'archive')
            with patch('special_function_agent.real_special._run_lean', return_value=ACCEPTED) as lean:
                result = archive.lookup(target(), 'direct', base/'archive')
            self.assertEqual(result['reused_record_id'], older['id'])
            self.assertEqual(lean.call_count, 1)
            self.assertEqual(result['skipped'][0]['record_id'], newer['id'])
            self.assertEqual(result['skipped'][0]['reason'], 'invalid_record')
            self.assertIn('changed', result['skipped'][0]['detail'])
            self.assertEqual(snapshot(base/'archive'), before)

    def test_rehashed_source_or_old_environment_is_rejected_before_lean(self):
        for tamper in ('source', 'environment'):
            with self.subTest(tamper=tamper), tempfile.TemporaryDirectory() as folder:
                base = Path(folder)
                record = store(base)
                entry = Path(record['record_dir'])
                result = load_json(entry/'verification/result.json')
                if tamper == 'source':
                    raw = 'axiom injected : False\n'
                    (entry/'verification/certificate.lean').write_text(raw)
                    result['certificate_sha256'] = hashlib.sha256(raw.encode()).hexdigest()
                else:
                    result['environment'] = {'lean-toolchain': 'old-environment'}
                    metadata = load_json(entry/'record.json')
                    metadata['environment'] = result['environment']
                    metadata['environment_sha256'] = archive._digest(archive._json_bytes(result['environment']))
                    (entry/'record.json').write_text(json.dumps(metadata))
                (entry/'verification/result.json').write_text(json.dumps(result))
                rehash(entry)
                before = snapshot(base/'archive')
                with patch('special_function_agent.real_special._run_lean') as lean:
                    found = archive.lookup(target(), 'direct', base/'archive')
                    lean.assert_not_called()
                self.assertEqual(found['status'], 'not_found')
                self.assertEqual(found['skipped'][0]['reason'], 'replay_failed')
                self.assertIn('environment' if tamper == 'environment' else 'certificate', found['skipped'][0]['detail'])
                self.assertEqual(snapshot(base/'archive'), before)

    def test_conditional_and_nonaccepted_replay_never_become_proved(self):
        with tempfile.TemporaryDirectory() as folder:
            base = Path(folder)
            cross = parse_identity((ROOT/'examples/cross-product-root.txt').read_text())
            request = {**cross, 'proof': {'mode': 'diagnostic'}}
            with patch('special_function_agent.real_bessel._run_lean', return_value=ACCEPTED), \
                    patch('special_function_agent.real_numeric.importlib.import_module', side_effect=ImportError):
                result = verify(request, base/'conditional')
                self.assertTrue(result['conditional_lean']['accepted'])
                record = archive.register_verification(base/'conditional', base/'archive')
            before = snapshot(base/'archive')
            with patch('special_function_agent.archive.replay_record') as replay:
                found = archive.lookup(cross, 'direct', base/'archive')
                replay.assert_not_called()
            self.assertEqual(found['status'], 'not_found')
            self.assertEqual(found['skipped'], [{'record_id': record['id'], 'reason': 'not_full_proof'}])
            self.assertEqual(snapshot(base/'archive'), before)
        for replay_result in ({'status': 'unresolved', 'replayed': False, 'verification': {'accepted': False}},
                              {'status': 'refuted', 'replayed': True, 'verification': ACCEPTED},
                              {'status': 'proved', 'replayed': True, 'verification': ACCEPTED, 'full_bessel_proof': False}):
            with self.subTest(result=replay_result), tempfile.TemporaryDirectory() as folder:
                base = Path(folder)
                store(base)
                with patch('special_function_agent.archive.replay_record', return_value=replay_result):
                    found = archive.lookup(target(), 'direct', base/'archive')
                self.assertEqual(found['status'], 'not_found')
                self.assertEqual(found['skipped'][0]['reason'], 'replay_rejected')

    def test_symlink_record_is_skipped_without_changing_external_evidence(self):
        with tempfile.TemporaryDirectory() as folder:
            base = Path(folder)
            record = store(base)
            certificate = Path(record['verification_dir'])/'certificate.lean'
            external = base/'external.lean'
            external.write_bytes(certificate.read_bytes())
            certificate.unlink()
            certificate.symlink_to(external)
            before = external.read_bytes()
            with patch('special_function_agent.real_special._run_lean') as lean:
                result = archive.lookup(target(), 'direct', base/'archive')
                lean.assert_not_called()
            self.assertEqual(result['status'], 'not_found')
            self.assertEqual(result['skipped'][0]['reason'], 'invalid_record')
            self.assertEqual(external.read_bytes(), before)
            self.assertTrue(certificate.is_symlink())


@unittest.skipUnless(os.environ.get('SF_RUN_LEAN_TESTS') == '1', 'Enable the real Lean archive lookup check.')
class ArchiveLookupLeanTests(unittest.TestCase):
    def test_cli_replays_actual_gamma_proof_without_writing_archive(self):
        with tempfile.TemporaryDirectory() as folder:
            base = Path(folder)
            data = target()
            request = {**data, 'proof': default_proof(data, 'steps')}
            result = verify(request, base/'verification', timeout=120)
            self.assertEqual(result['status'], 'proved')
            record = archive.register_verification(base/'verification', base/'archive', timeout=120)
            source = base/'target.json'
            source.write_text(json.dumps(data))
            before = snapshot(base/'archive')
            checked = subprocess.run([sys.executable, '-m', 'special_function_agent', 'archive', 'lookup',
                                      str(source), '--route', 'steps', '--archive-dir', str(base/'archive'),
                                      '--timeout', '120'], cwd=ROOT, capture_output=True, text=True, timeout=150)
            self.assertEqual(checked.returncode, 0, checked.stdout+checked.stderr)
            found = json.loads(checked.stdout)
            self.assertEqual(found['status'], 'proved')
            self.assertTrue(found['replayed'])
            self.assertFalse(found['ai_called'])
            self.assertEqual(found['reused_record_id'], record['id'])
            self.assertTrue(found['verification']['accepted'])
            self.assertLessEqual(set(found['verification']['axioms']), set(ACCEPTED['axioms']))
            self.assertEqual(snapshot(base/'archive'), before)


if __name__ == '__main__':
    unittest.main()
