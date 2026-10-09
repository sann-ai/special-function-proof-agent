"""Special-function archive isolation, exact targets, and explicit Bessel import."""
import copy
import hashlib
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

from special_function_agent import archive, registry
from special_function_agent.core import InputError, ROOT, load_json, verify
from special_function_agent.parser import parse_identity
from special_function_agent.real_special import default_proof


ACCEPTED = {'accepted': True, 'axioms': ['Classical.choice', 'Quot.sound', 'propext']}
CURRENT_ENVIRONMENT = {'lean-toolchain': 'new-verified-environment', 'registry': 'current'}
GAMMA = 'Gamma(x+1)=x*Gamma(x); x>0'
BETA = 'int(0,1,t^(a-1)*(1-t)^(b-1),t)=Gamma(a)*Gamma(b)/Gamma(a+b); a>0,b>0'


def gamma_request():
    target = parse_identity(GAMMA)
    return {**target, 'proof': default_proof(target)}


def snapshot(directory):
    return {path.relative_to(directory).as_posix(): path.read_bytes()
            for path in directory.rglob('*') if path.is_file()}


class SpecialArchiveTests(unittest.TestCase):
    def test_default_and_environment_roots_are_isolated_from_bessel(self):
        with tempfile.TemporaryDirectory() as folder:
            base = Path(folder).resolve()
            old = base/'BesselProofAgentData'/'archive'
            chosen = base/'chosen'
            with patch.dict(os.environ, {'BESSEL_ARCHIVE_DIR': str(old)}, clear=True), patch('pathlib.Path.home', return_value=base):
                expected = base/'SpecialFunctionProofAgentData'/'archive'
                self.assertEqual(archive.resolve_archive_root(), expected)
                self.assertEqual(archive.list_records(), [])
                self.assertFalse(expected.exists())
                self.assertFalse(old.exists())
                with patch.dict(os.environ, {'SPECIAL_FUNCTION_ARCHIVE_DIR': str(chosen)}):
                    self.assertEqual(archive.resolve_archive_root(), chosen)
                    self.assertEqual(archive.resolve_archive_root(base/'explicit'), base/'explicit')
                self.assertEqual(archive.resolve_archive_root(), expected)

    def test_v2_identity_tracks_names_types_conditions_and_registry(self):
        original = parse_identity(BETA)
        key = archive.target_hash(original)
        reordered = copy.deepcopy(original)
        reordered['assumptions'].reverse()
        reordered['variables'] = dict(reversed(list(reordered['variables'].items())))
        self.assertEqual(key, archive.target_hash(reordered))
        self.assertEqual(key, archive.target_hash({**original, 'proof': {'mode': 'diagnostic'}}))
        renamed = parse_identity(BETA.replace('b', 'shape'))
        self.assertNotEqual(key, archive.target_hash(renamed))
        with_extra = parse_identity(BETA+',a!=2,Gamma(a-1)!=0')
        self.assertNotEqual(key, archive.target_hash(with_extra))
        self.assertEqual(archive.canonical_target(with_extra)['variables'], {'a': 'real', 'b': 'real'})
        for kind in ('int', 'complex', True):
            invalid = copy.deepcopy(original)
            invalid['variables']['a'] = kind
            with self.subTest(kind=kind), self.assertRaises(InputError):
                archive.target_hash(invalid)
        conventions = copy.deepcopy(registry.CONVENTIONS)
        conventions['finite_integral'] = 'changed integration convention'
        with patch.object(registry, 'CONVENTIONS', conventions):
            self.assertNotEqual(key, archive.target_hash(original))

    def test_integral_binding_and_endpoints_are_part_of_exact_identity(self):
        original = parse_identity(BETA)
        renamed = parse_identity(BETA.replace('t^', 'u^').replace('(1-t)', '(1-u)').replace(',t)', ',u)'))
        changed_endpoint = copy.deepcopy(original)
        changed_endpoint['lhs']['upper'] = {'op': 'int', 'value': 2}
        self.assertEqual(original['variables'], renamed['variables'])
        self.assertNotEqual(archive.target_hash(original), archive.target_hash(renamed))
        self.assertNotEqual(archive.target_hash(original), archive.target_hash(changed_endpoint))
        invalid = copy.deepcopy(original)
        invalid['lhs']['var'] = 'a'
        with self.assertRaises(InputError):
            archive.target_hash(invalid)

    def test_gamma_proof_registration_and_replay_do_not_need_mpmath(self):
        with tempfile.TemporaryDirectory() as folder:
            base = Path(folder)
            with patch('special_function_agent.real_special._run_lean', return_value=ACCEPTED) as lean, patch('special_function_agent.real_numeric.importlib.import_module', side_effect=ImportError):
                result = verify(gamma_request(), base/'run')
                self.assertEqual(result['status'], 'proved')
                self.assertTrue(result['full_function_proof'])
                self.assertEqual(result['numerical']['diagnostic'], 'backend_unavailable')
                record = archive.register_verification(base/'run', base/'archive', original_input=GAMMA)
                replayed = archive.replay_record(record['id'], base/'archive')
            self.assertTrue(replayed['replayed'])
            self.assertEqual(lean.call_count, 3)
            self.assertNotEqual(lean.call_args_list[0].args[0].parent, lean.call_args_list[1].args[0].parent)
            self.assertEqual(record['request'], gamma_request())
            self.assertEqual(record['original_input'], GAMMA)
            self.assertEqual(record['canonical_target']['conventions'], registry.CONVENTIONS)
            evidence = Path(record['verification_dir'])
            self.assertEqual(load_json(evidence/'numerical.json')['diagnostic'], 'backend_unavailable')
            self.assertTrue((evidence/'certificate.lean').is_file())

    def test_cross_conditional_evidence_is_saved_without_mpmath(self):
        target = parse_identity((ROOT/'examples/cross-product-root.txt').read_text())
        request = {**target, 'proof': {'mode': 'diagnostic'}}
        with tempfile.TemporaryDirectory() as folder:
            base = Path(folder)
            with patch('special_function_agent.real_bessel._run_lean', return_value=ACCEPTED) as lean, patch('special_function_agent.real_numeric.importlib.import_module', side_effect=ImportError):
                result = verify(request, base/'run')
                record = archive.register_verification(base/'run', base/'archive')
                replayed = archive.replay_record(record['id'], base/'archive')
            self.assertEqual(result['status'], 'unresolved')
            self.assertFalse(result['full_bessel_proof'])
            self.assertEqual(result['numerical']['diagnostic'], 'backend_unavailable')
            self.assertTrue(result['conditional_lean']['accepted'])
            self.assertFalse(replayed['replayed'])
            self.assertTrue(replayed['conditional_replayed'])
            self.assertEqual(lean.call_count, 2)
            evidence = Path(record['verification_dir'])
            self.assertEqual((evidence/'conditional_certificate.lean').read_bytes(), (base/'run'/'conditional_certificate.lean').read_bytes())
            self.assertEqual(archive.find_exact(target, base/'archive')[0]['id'], record['id'])

    def test_explicit_bessel_import_reverifies_and_preserves_source_environment(self):
        source = ROOT/'demo/direct'
        before = snapshot(source)
        previous = load_json(source/'result.json')
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)/'archive'
            with patch('special_function_agent.core.environment', return_value=CURRENT_ENVIRONMENT), patch('special_function_agent.core._run_lean', return_value=ACCEPTED) as lean:
                self.assertEqual(archive.list_records(root), [])
                self.assertFalse(root.exists())
                record = archive.import_bessel(source, root)
                replayed = archive.replay_record(record['id'], root)
            self.assertTrue(replayed['replayed'])
            self.assertEqual(lean.call_count, 3)
            self.assertEqual(record['environment'], CURRENT_ENVIRONMENT)
            self.assertEqual(record['result']['environment'], CURRENT_ENVIRONMENT)
            provenance = record['provenance']
            self.assertEqual(provenance['provider'], 'explicit_bessel_import')
            self.assertEqual(provenance['upstream_repository'], 'https://github.com/sann-ai/bessel-proof-agent')
            self.assertEqual(provenance['source_environment'], previous['environment'])
            self.assertEqual(provenance['source_status'], previous['status'])
            self.assertEqual(provenance['source_request_sha256'], hashlib.sha256(before['request.json']).hexdigest())
            self.assertEqual(provenance['source_result_sha256'], hashlib.sha256(before['result.json']).hexdigest())
            self.assertEqual(record['request'], load_json(source/'request.json'))
        self.assertEqual(before, snapshot(source))

    def test_legacy_bessel_v2_archive_identity_is_imported_explicitly(self):
        # Recreate the original archive's v2 identity, before this project's conventions field.
        with tempfile.TemporaryDirectory() as folder:
            base = Path(folder)
            old = archive.register_verification(ROOT/'demo/cross-product', base/'old')
            entry = Path(old['record_dir'])
            legacy = archive.canonical_target(old['request'])
            legacy.pop('conventions')
            metadata = load_json(entry/'record.json')
            metadata['target_sha256'] = archive._digest(archive._json_bytes(legacy))
            (entry/'record.json').write_text(json.dumps(metadata))
            manifest = load_json(entry/'manifest.json')
            manifest['files']['record.json'] = archive._digest((entry/'record.json').read_bytes())
            (entry/'manifest.json').write_text(json.dumps(manifest))
            before = snapshot(entry)
            # The normal independent archive reader keeps its stronger identity contract.
            with self.assertRaises(InputError):
                archive.show_record(old['id'], base/'old')
            with patch('special_function_agent.real_bessel._run_lean', return_value=ACCEPTED), \
                 patch('special_function_agent.real_numeric.importlib.import_module', side_effect=ImportError):
                imported = archive.import_bessel(entry, base/'new')
                self.assertEqual(imported['status'], 'unresolved')
                self.assertFalse(imported['result']['full_bessel_proof'])
                self.assertTrue(imported['result']['conditional_lean']['accepted'])
                self.assertEqual(imported['provenance']['source_environment'], metadata['environment'])
            self.assertEqual(before, snapshot(entry))
            with (entry/'verification'/'request.json').open('a') as stream:
                stream.write('\n')
            with patch('special_function_agent.real_bessel._run_lean') as lean:
                with self.assertRaisesRegex(InputError, 'changed'):
                    archive.import_bessel(entry, base/'rejected')
                lean.assert_not_called()

    def test_import_rejects_changed_request_certificate_and_hashes_before_lean(self):
        for tamper in ('request', 'certificate', 'certificate_hash'):
            with self.subTest(tamper=tamper), tempfile.TemporaryDirectory() as folder:
                base = Path(folder)
                source = base/'source'
                shutil.copytree(ROOT/'demo/direct', source)
                if tamper == 'request':
                    data = load_json(source/'request.json')
                    data['rhs'] = {'op': 'int', 'value': 3}
                    (source/'request.json').write_text(json.dumps(data))
                elif tamper == 'certificate':
                    with (source/'certificate.lean').open('a') as stream:
                        stream.write('\n-- modified evidence\n')
                else:
                    data = load_json(source/'result.json')
                    data['certificate_sha256'] = '0'*64
                    (source/'result.json').write_text(json.dumps(data))
                with patch('special_function_agent.core._run_lean') as lean:
                    with self.assertRaises(InputError):
                        archive.import_bessel(source, base/'archive')
                lean.assert_not_called()
                self.assertFalse((base/'archive').exists())

    def test_import_checks_archive_manifest_before_reverification(self):
        with tempfile.TemporaryDirectory() as folder:
            base = Path(folder)
            with patch('special_function_agent.archive.replay', return_value={'status': 'proved', 'replayed': True}):
                previous = archive.register_verification(ROOT/'demo/direct', base/'old-archive')
            source = Path(previous['record_dir'])
            with (source/'verification'/'certificate.lean').open('a') as stream:
                stream.write('\n-- changed archived evidence\n')
            with patch('special_function_agent.core._run_lean') as lean:
                with self.assertRaisesRegex(InputError, 'changed'):
                    archive.import_bessel(source, base/'new-archive')
            lean.assert_not_called()
            self.assertFalse((base/'new-archive').exists())

    def test_special_certificate_tampering_is_rejected_before_replay(self):
        with tempfile.TemporaryDirectory() as folder:
            base = Path(folder)
            with patch('special_function_agent.real_special._run_lean', return_value=ACCEPTED), patch('special_function_agent.real_numeric.importlib.import_module', side_effect=ImportError):
                verify(gamma_request(), base/'run')
                record = archive.register_verification(base/'run', base/'archive')
            evidence = Path(record['verification_dir'])/'certificate.lean'
            evidence.write_text(evidence.read_text()+'\n-- changed\n')
            with patch('special_function_agent.real_special._run_lean') as lean:
                with self.assertRaisesRegex(InputError, 'changed'):
                    archive.replay_record(record['id'], base/'archive')
            lean.assert_not_called()


@unittest.skipUnless(os.environ.get('SF_RUN_LEAN_TESTS') == '1', 'Enable real Lean archive replay checks.')
class SpecialArchiveLeanTests(unittest.TestCase):
    def test_gamma_archive_replays_with_numerical_backend_unavailable(self):
        with tempfile.TemporaryDirectory() as folder:
            base = Path(folder)
            with patch('special_function_agent.real_numeric.importlib.import_module', side_effect=ImportError):
                result = verify(gamma_request(), base/'run', timeout=120)
                self.assertEqual(result['status'], 'proved', result)
                record = archive.register_verification(base/'run', base/'archive', timeout=120)
                self.assertTrue(archive.replay_record(record['id'], base/'archive', timeout=120)['replayed'])


if __name__ == '__main__':
    unittest.main()
