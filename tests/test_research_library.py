"""Research transport preserves exact evidence and executes only regenerated proofs."""
from contextlib import contextmanager
from copy import deepcopy
from importlib import import_module
import hashlib
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from special_function_agent import core, research_library as library
from special_function_agent.parser import parse_identity
from special_function_agent.real_special import default_proof, render

ACCEPTED = {'accepted': True, 'axioms': sorted(core.ALLOWED_AXIOMS),
            'stdout': "BESSEL_AUDIT_BEGIN\n'BesselAgentCandidate.target' depends on axioms: [Classical.choice, Quot.sound, propext]\nBESSEL_AUDIT_END\n"}
GAMMA = 'Gamma(x+1)=x*Gamma(x);x>0'


def request(text=GAMMA, diagnostic=False):
    target = parse_identity(text)
    return {**target, 'proof': {'mode': 'diagnostic'} if diagnostic else default_proof(target)}


def encoded(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(',', ':'), allow_nan=False).encode('utf-8')


def repack(package):
    package = deepcopy(package)
    package['manifest'] = {name: hashlib.sha256(text.encode('utf-8')).hexdigest()
                           for name, text in package['evidence'].items()}
    package.pop('id', None)
    package['id'] = hashlib.sha256(encoded(package)).hexdigest()
    return package


def change_result(package, update):
    package = deepcopy(package)
    result = json.loads(package['evidence']['result.json'])
    update(result)
    package['evidence']['result.json'] = json.dumps(result)
    return repack(package)


def derived_request(package, mode='direct'):
    target = parse_identity(GAMMA)
    uses = [{'lemma': package['id'], 'arguments': {'x': {'op': 'var', 'name': 'x'}}, 'reverse': False}]
    if mode == 'direct':
        proof = {'mode': 'direct', 'recipe': 'research', 'uses': uses, 'lemmas': [package]}
    else:
        proof = {'mode': 'steps', 'lemmas': [package], 'steps': [
            {'before': target['lhs'], 'after': target['rhs'], 'recipe': 'research', 'uses': uses,
             'reason': '保存した補題を元の正値条件で適用する。', 'conditions': ['x > 0']}]}
    return {**target, 'proof': proof}


def minimal_package(name, data):
    return repack({'schema_version': 1, 'name': name, 'source': None, 'original_input': None,
                   'evidence': {'request.json': json.dumps(data),
                                'result.json': json.dumps({'status': 'proved', 'full_function_proof': True}),
                                'certificate.lean': 'untrusted transport text'}, 'manifest': {}})


def snapshot(directory):
    return {p.relative_to(directory).as_posix(): p.read_bytes()
            for p in directory.rglob('*') if p.is_file()}


def without_mpmath(name, *args, **kwargs):
    if name == 'mpmath':
        raise ImportError('optional numerical backend unavailable')
    return import_module(name, *args, **kwargs)


@contextmanager
def fake_lean():
    with patch('special_function_agent.real_special._run_lean', return_value=ACCEPTED) as special, \
         patch('special_function_agent.real_bessel._run_lean', return_value=ACCEPTED) as bessel, \
         patch('special_function_agent.real_numeric.importlib.import_module', side_effect=without_mpmath):
        yield special, bessel


class ResearchLibraryTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='research-library-test-')
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name).resolve()
        self.root = self.base/'library'

    def full_package(self, name='Gamma-recurrence', data=None):
        output = self.base/(name+'-run')
        core.verify(data or request(), output)
        return library.register(output, self.root, name=name, source='https://example.org/lemma', original_input=GAMMA)

    def external(self, package, name='export.json'):
        path = self.base/name
        path.write_bytes(encoded(package)+b'\n')
        return path

    def test_default_root_environment_and_repository_boundaries(self):
        with patch.dict(os.environ, {'SPECIAL_FUNCTION_ARCHIVE_DIR': str(self.base/'archive'),
                                     'BESSEL_ARCHIVE_DIR': str(self.base/'legacy')}, clear=True), \
             patch('pathlib.Path.home', return_value=self.base):
            expected = self.base/'SpecialFunctionProofAgentData/research'
            self.assertEqual(library.resolve_library_root(), expected)
            self.assertEqual(library.list_entries(), [])
            self.assertFalse(expected.exists())
            with patch.dict(os.environ, {'SPECIAL_FUNCTION_RESEARCH_DIR': str(self.root)}):
                self.assertEqual(library.resolve_library_root(), self.root)
                self.assertEqual(library.resolve_library_root(self.base/'explicit'), self.base/'explicit')
        for root in (core.ROOT, core.ROOT/'research'):
            with self.assertRaises(core.InputError):
                library.resolve_library_root(root)
        linked = self.base/'linked-repository'
        linked.symlink_to(core.ROOT, target_is_directory=True)
        with self.assertRaises(core.InputError):
            library.resolve_library_root(linked/'data')
        self.assertEqual(list(self.base.iterdir()), [linked])

    def test_register_export_import_replay_copy_and_append_only(self):
        with fake_lean() as (lean, _):
            package = self.full_package()
            self.assertEqual(lean.call_count, 2)
            self.assertNotEqual(lean.call_args_list[0].args[0].parent, lean.call_args_list[1].args[0].parent)
            stored = self.root/(package['id']+'.json')
            before = stored.read_bytes()
            self.assertEqual(library.load(package['id'], self.root), package)
            self.assertEqual(library.list_entries(self.root), [package])
            destination = self.base/'out'/'chosen.json'
            exported = library.export(package['id'], destination, self.root)
            self.assertEqual(exported, {'id': package['id'], 'path': str(destination)})
            imported = library.import_package(destination, self.base/'second')
            self.assertEqual(imported, package)
            self.assertEqual(lean.call_count, 3)
            self.assertEqual(library.import_package(destination, self.base/'second'), package)
            with self.assertRaises(core.InputError):
                library.export(package['id'], destination, self.root)
            self.assertEqual(stored.read_bytes(), before)
            self.assertEqual(destination.read_bytes(), before)
            self.assertEqual((self.base/'second'/stored.name).read_bytes(), before)
            self.assertEqual(library.read_evidence_json(package, 'request.json'), request())
            self.assertEqual(library.read_evidence_json(package, 'numerical.json')['diagnostic'], 'backend_unavailable')

    def test_pure_validation_does_not_check_environment_or_run_lean(self):
        with fake_lean():
            package = self.full_package()
        package = change_result(package, lambda result: result.update(environment={'old': 'environment'}))
        with patch.object(core, 'environment', side_effect=AssertionError('environment access')), \
             patch.object(core, 'replay', side_effect=AssertionError('replay')):
            self.assertIs(library.validate_package(package), package)
            self.assertEqual(library.read_evidence_json(package, 'result.json')['environment'], {'old': 'environment'})
        for filename in ('../request.json', 'certificate.lean', 'absent.json', []):
            with self.subTest(filename=filename), self.assertRaises(core.InputError):
                library.read_evidence_json(package, filename)

    def test_unresolved_evidence_is_recorded_without_executing_lean(self):
        directory = self.base/'unresolved'
        directory.mkdir()
        (directory/'request.json').write_text(json.dumps(request()))
        (directory/'result.json').write_text(json.dumps({'status': 'unresolved', 'full_function_proof': False,
                                                       'numerical': {'diagnostic': 'backend_unavailable'}}))
        payload = '#eval IO.println "untrusted raw Lean metadata"\n'
        (directory/'proof_attempt.lean').write_text(payload)
        with patch.object(core, 'replay') as replay:
            package = library.register(directory, self.root, name='Unresolved')
            imported = library.import_package(self.external(package), self.base/'imported')
            replay.assert_not_called()
        self.assertEqual(imported['evidence']['proof_attempt.lean'], payload)
        self.assertEqual(library.read_evidence_json(imported, 'result.json')['status'], 'unresolved')

    def test_numeric_and_condition_statuses_are_preserved_without_replay(self):
        for status in ('needs_conditions', 'unresolved'):
            directory = self.base/status
            directory.mkdir()
            (directory/'request.json').write_text(json.dumps(request()))
            result = {'status': status, 'full_function_proof': False,
                      'numerical': {'diagnostic': 'numerical_counterexample', 'samples': [1, 2]}}
            (directory/'result.json').write_text(json.dumps(result))
            with patch.object(core, 'replay') as replay:
                package = library.register(directory, self.root, name=status)
                self.assertEqual(library.read_evidence_json(package, 'result.json'), result)
                replay.assert_not_called()

    def test_conditional_scope_is_replayed_and_cannot_be_promoted(self):
        data = request((core.ROOT/'examples/cross-product-root.txt').read_text(), diagnostic=True)
        with fake_lean() as (_, lean):
            package = self.full_package('Cross-conditional', data)
            self.assertEqual(lean.call_count, 2)
            result = library.read_evidence_json(package, 'result.json')
            self.assertEqual(result['status'], 'unresolved')
            self.assertFalse(result['full_bessel_proof'])
            self.assertTrue(result['conditional_lean']['accepted'])
        for field in ('scope', 'assumptions', 'full_bessel_proof', 'status'):
            changed = deepcopy(package)
            result = json.loads(changed['evidence']['result.json'])
            if field in {'scope', 'assumptions'}:
                result['conditional_lean'][field] = 'unconditional' if field == 'scope' else []
            elif field == 'status':
                result.update(status='proved', full_function_proof=True)
            else:
                result[field] = True
            changed['evidence']['result.json'] = json.dumps(result)
            changed = repack(changed)
            with self.subTest(field=field), fake_lean() as (special, lean):
                with self.assertRaises(core.InputError):
                    library.import_package(self.external(changed), self.base/'bad')
                lean.assert_not_called()
                special.assert_not_called()
            self.assertFalse((self.base/'bad').exists())

    def test_rehashed_arbitrary_lean_is_rejected_before_execution(self):
        with fake_lean():
            package = self.full_package()
        changed = deepcopy(package)
        source = changed['evidence']['certificate.lean']+'\n#eval IO.println "arbitrary code"\n'
        changed['evidence']['certificate.lean'] = source
        result = json.loads(changed['evidence']['result.json'])
        result['certificate_sha256'] = hashlib.sha256(source.encode()).hexdigest()
        changed['evidence']['result.json'] = json.dumps(result)
        changed = repack(changed)
        with fake_lean() as (lean, _):
            with self.assertRaisesRegex(core.InputError, 'certificate'):
                library.import_package(self.external(changed), self.base/'bad')
            lean.assert_not_called()
        self.assertFalse((self.base/'bad').exists())

    def test_rehashed_full_scope_change_is_rejected_before_lean(self):
        with fake_lean():
            package = self.full_package()
        changed = change_result(package, lambda result: result.update(formal_scope='unconditional gamma identity'))
        with fake_lean() as (lean, _):
            with self.assertRaisesRegex(core.InputError, 'scope'):
                library.import_package(self.external(changed), self.base/'bad')
            lean.assert_not_called()

    def test_rehashed_target_change_and_environment_change_are_rejected(self):
        with fake_lean():
            package = self.full_package()
        for kind in ('target', 'environment', 'conventions'):
            changed = deepcopy(package)
            if kind == 'target':
                data = json.loads(changed['evidence']['request.json'])
                data['rhs'] = {'op': 'int', 'value': 0}
                changed['evidence']['request.json'] = json.dumps(data)
                result = json.loads(changed['evidence']['result.json'])
                result['request_sha256'] = hashlib.sha256(changed['evidence']['request.json'].encode()).hexdigest()
                changed['evidence']['result.json'] = json.dumps(result)
                changed = repack(changed)
            else:
                changed = change_result(changed, lambda result: result.update({kind: {'changed': True}}))
            with self.subTest(kind=kind), fake_lean() as (lean, _):
                with self.assertRaises(core.InputError):
                    library.import_package(self.external(changed), self.base/'bad')
                lean.assert_not_called()

    def test_explicit_reverify_preserves_old_bytes_target_and_diagnostic_scope(self):
        with fake_lean():
            package = self.full_package()
        old = snapshot(self.root)
        next_environment = {**core.environment(), 'future-foundation': 'new'}
        with fake_lean(), patch('special_function_agent.real_special.environment', return_value=next_environment):
            with self.assertRaisesRegex(core.InputError, 'environment'):
                library.import_package(self.external(package), self.base/'rejected')
            rechecked = library.reverify(package['id'], self.root)
        new = rechecked['package']
        self.assertEqual(rechecked['previous_id'], package['id'])
        self.assertNotEqual(new['id'], package['id'])
        self.assertEqual(library.read_evidence_json(new, 'request.json'), request())
        self.assertEqual(library.read_evidence_json(new, 'result.json')['environment'], next_environment)
        for name, raw in old.items():
            self.assertEqual((self.root/name).read_bytes(), raw)
        self.assertEqual(len(library.list_entries(self.root)), 2)
        data = request((core.ROOT/'examples/cross-product-root.txt').read_text(), diagnostic=True)
        with fake_lean():
            conditional = self.full_package('Conditional', data)
        original = library.read_evidence_json(conditional, 'result.json')
        with fake_lean(), patch('special_function_agent.real_bessel.environment', return_value=next_environment):
            rechecked = library.reverify(conditional['id'], self.root)['package']
        updated = library.read_evidence_json(rechecked, 'result.json')
        self.assertEqual(library.read_evidence_json(rechecked, 'request.json'), data)
        self.assertEqual(updated['status'], original['status'])
        self.assertEqual(updated['conditional_lean']['scope'], original['conditional_lean']['scope'])
        self.assertEqual(updated['conditional_lean']['assumptions'], original['conditional_lean']['assumptions'])
        self.assertFalse(updated['full_bessel_proof'])

    def test_external_reverify_uses_request_and_never_executes_old_source(self):
        with fake_lean():
            package = self.full_package()
        changed = deepcopy(package)
        changed['evidence']['certificate.lean'] = '#eval IO.println "never execute this"\n'
        changed = change_result(changed, lambda result: result.update(environment={'old': 'foundation'}))
        path = self.external(changed)
        before = path.read_bytes()
        sources = []
        def check(path, timeout):
            sources.append(path.read_text())
            self.assertEqual(path.read_text(), render(request()))
            return ACCEPTED
        with fake_lean(), patch('special_function_agent.real_special._run_lean', side_effect=check):
            rechecked = library.reverify_package(path, self.base/'fresh')
        self.assertEqual(len(sources), 2)
        self.assertEqual(rechecked['previous_id'], changed['id'])
        self.assertEqual(library.read_evidence_json(rechecked['package'], 'result.json')['status'], 'proved')
        self.assertEqual(path.read_bytes(), before)

    def test_nested_reverify_refreshes_direct_and_steps_ids_and_only_stores_parent(self):
        with fake_lean():
            leaf = self.full_package('Leaf')
            middle = self.full_package('Middle', derived_request(leaf))
            parent = self.full_package('Parent', derived_request(middle, 'steps'))
        before = snapshot(self.root)
        updated_environment = {**core.environment(), 'updated-foundation': 'revision'}
        with fake_lean() as (lean, _), \
             patch('special_function_agent.real_special.environment', return_value=updated_environment), \
             patch('special_function_agent.research_proof.environment', return_value=updated_environment):
            result = library.reverify(parent['id'], self.root)
            self.assertEqual(lean.call_count, 4)
        current = result['package']
        self.assertEqual(result['previous_id'], parent['id'])
        for original in (parent, middle, leaf):
            current_data = library.read_evidence_json(current, 'request.json')
            original_data = library.read_evidence_json(original, 'request.json')
            self.assertEqual({k: v for k, v in current_data.items() if k != 'proof'},
                             {k: v for k, v in original_data.items() if k != 'proof'})
            self.assertNotEqual(current['id'], original['id'])
            self.assertEqual(current['name'], original['name'])
            self.assertEqual(current['source'], original['source'])
            self.assertEqual(library.read_evidence_json(current, 'result.json')['environment'], updated_environment)
            proof = current_data['proof']
            if 'lemmas' in proof:
                child = proof['lemmas'][0]
                uses = proof['uses'] if proof['mode'] == 'direct' else proof['steps'][0]['uses']
                self.assertEqual(uses[0]['lemma'], child['id'])
                self.assertNotEqual(uses[0]['lemma'], original_data['proof']['lemmas'][0]['id'])
                current = child
        after = snapshot(self.root)
        self.assertEqual(len(after), len(before)+1)
        for name, raw in before.items():
            self.assertEqual(after[name], raw)

    def test_failed_dependency_reverify_keeps_entire_library_unchanged(self):
        with fake_lean():
            leaf = self.full_package('Leaf')
            parent = self.full_package('Parent', derived_request(leaf))
        before = snapshot(self.root)
        with fake_lean(), patch('special_function_agent.real_special._run_lean', return_value={'accepted': False, 'reason': 'timeout'}):
            with self.assertRaisesRegex(core.InputError, 'did not prove'):
                library.reverify(parent['id'], self.root)
        self.assertEqual(snapshot(self.root), before)

    def test_dependency_limits_and_unknown_references_fail_before_verification(self):
        leaf = minimal_package('Leaf', request())
        too_deep = leaf
        for depth in range(4):
            too_deep = minimal_package('Level'+str(depth), derived_request(too_deep))
        too_many = derived_request(leaf)
        too_many['proof']['lemmas'] = [minimal_package('Leaf'+str(index), request()) for index in range(13)]
        missing = derived_request(leaf)
        missing['proof']['uses'][0]['lemma'] = '0'*64
        repeated = derived_request(leaf)
        repeated['proof']['lemmas'].append(leaf)
        for package in (too_deep, minimal_package('TooMany', too_many),
                        minimal_package('Missing', missing), minimal_package('Repeated', repeated)):
            with self.subTest(name=package['name']), patch.object(core, 'verify') as verify:
                with self.assertRaises(core.InputError):
                    library.reverify_package(self.external(package), self.base/'absent')
                verify.assert_not_called()
                self.assertFalse((self.base/'absent').exists())

    def test_shape_names_unknown_status_and_v1_are_rejected(self):
        with fake_lean():
            package = self.full_package()
        for name in ('../escape', '/absolute', 'a/b', 'a.b', '', '0bad', 'Gamma x', 'γ', 'a'*65):
            changed = deepcopy(package)
            changed['name'] = name
            with self.subTest(name=name), self.assertRaises(core.InputError):
                library.validate_package(repack(changed))
        for field, value in (('schema_version', True), ('source', {}), ('original_input', [])):
            changed = deepcopy(package)
            changed[field] = value
            with self.subTest(field=field), self.assertRaises(core.InputError):
                library.validate_package(repack(changed))
        for status in ('numerically_proved', '', None, True):
            changed = change_result(package, lambda result: result.update(status=status))
            with self.subTest(status=status), patch.object(core, 'replay') as replay:
                with self.assertRaises(core.InputError):
                    library.import_package(self.external(changed), self.base/'bad')
                replay.assert_not_called()
        changed = deepcopy(package)
        changed['evidence']['request.json'] = json.dumps({'schema_version': 1})
        with self.assertRaisesRegex(core.InputError, 'version 1'):
            library.import_package(self.external(repack(changed)), self.base/'bad')
        with self.assertRaises(core.InputError):
            library.load(package['name'], self.root)

    def test_manifest_id_unknown_files_and_surrogate_text_are_rejected(self):
        with fake_lean():
            package = self.full_package()
        mutations = []
        changed = deepcopy(package); changed['id'] = '0'*64; mutations.append(changed)
        changed = deepcopy(package); changed['extra'] = True; mutations.append(changed)
        changed = deepcopy(package); changed['manifest']['request.json'] = '0'*64; mutations.append(changed)
        changed = deepcopy(package); changed['manifest'].pop('result.json'); mutations.append(changed)
        changed = deepcopy(package); changed['source'] = '\ud800'; mutations.append(changed)
        for name in ('../outside', '/absolute', 'sub/request.json', 'extra.lean'):
            changed = deepcopy(package); changed['evidence'][name] = 'text'; mutations.append(repack(changed))
        for changed in mutations:
            with self.subTest(keys=list(changed)), self.assertRaises(core.InputError):
                library.validate_package(changed)

    def test_duplicate_json_keys_nonfinite_values_and_nonobjects_are_rejected(self):
        with fake_lean():
            package = self.full_package()
        for text in ('{"a":1,"a":2}', '{"a":NaN}', '{"a":1e9999}', '{"a":"\\ud800"}', '{broken'):
            changed = deepcopy(package)
            changed['evidence']['request.json'] = text
            with self.subTest(text=text), self.assertRaises(core.InputError):
                library.validate_package(repack(changed))
        changed = deepcopy(package); changed['evidence']['request.json'] = '[]'
        with self.assertRaises(core.InputError):
            library.read_evidence_json(repack(changed), 'request.json')
        path = self.base/'duplicate.json'
        raw = encoded(package).decode()
        path.write_text('{"id":"'+package['id']+'",'+raw[1:])
        with patch.object(core, 'replay') as replay:
            with self.assertRaisesRegex(core.InputError, 'Duplicate'):
                library.import_package(path, self.base/'bad')
            replay.assert_not_called()

    def test_size_limits_apply_to_transport_evidence_and_metadata(self):
        with fake_lean():
            package = self.full_package()
        changed = deepcopy(package)
        changed['original_input'] = 'a'*library.MAX_PACKAGE_BYTES
        with self.assertRaisesRegex(core.InputError, '256 KiB'):
            library.validate_package(repack(changed))
        huge = self.base/'huge.json'; huge.write_bytes(b' '*(library.MAX_PACKAGE_BYTES+1))
        with self.assertRaisesRegex(core.InputError, '256 KiB'):
            library.import_package(huge, self.root)
        directory = self.base/'huge-evidence'; directory.mkdir()
        (directory/'report.md').write_bytes(b'a'*(library.MAX_PACKAGE_BYTES+1))
        with self.assertRaisesRegex(core.InputError, '256 KiB'):
            library.register(directory, self.root, name='Huge')

    def test_symlinks_unknown_directory_files_and_overwrite_are_rejected(self):
        with fake_lean():
            package = self.full_package()
        stored = self.root/(package['id']+'.json')
        for selected in ('root', 'package', 'export', 'evidence', 'verification'):
            link = self.base/('link-'+selected)
            if selected == 'root':
                link.symlink_to(self.root, target_is_directory=True)
                operation = lambda: library.load(package['id'], link)
            elif selected == 'package':
                link.symlink_to(stored)
                operation = lambda: library.import_package(link, self.base/'bad')
            elif selected == 'export':
                link.symlink_to(self.base/'new.json')
                operation = lambda: library.export(package['id'], link, self.root)
            elif selected == 'verification':
                link.symlink_to(self.base/'Gamma-recurrence-run', target_is_directory=True)
                operation = lambda: library.register(link, self.root, name='Linked')
            else:
                directory = self.base/'linked-evidence'; directory.mkdir()
                (directory/'request.json').symlink_to(self.base/'Gamma-recurrence-run'/'request.json')
                operation = lambda: library.register(directory, self.root, name='Linked')
            with self.subTest(selected=selected), self.assertRaises(core.InputError):
                operation()
        directory = self.base/'extra-file'; directory.mkdir(); (directory/'secret.txt').write_text('not evidence')
        with self.assertRaises(core.InputError):
            library.register(directory, self.root, name='Extra')
        with self.assertRaises(core.InputError):
            library.export(package['id'], core.ROOT/'research-export.json', self.root)
        before = stored.read_bytes()
        stored.write_bytes(before.replace(b'Gamma-recurrence', b'Gamma-CHANGED'))
        with self.assertRaises(core.InputError):
            library.load(package['id'], self.root)


@unittest.skipUnless(os.environ.get('SF_RUN_LEAN_TESTS') == '1', 'Enable real Lean research-library checks.')
class ResearchLibraryLeanTests(unittest.TestCase):
    def test_gamma_full_and_conditional_roundtrip_without_numerical_backend(self):
        with tempfile.TemporaryDirectory(prefix='research-library-lean-') as temporary, \
             patch('special_function_agent.real_numeric.importlib.import_module', side_effect=without_mpmath):
            base = Path(temporary)
            cases = [('Gamma', request()), ('Cross', request((core.ROOT/'examples/cross-product-root.txt').read_text(), diagnostic=True))]
            for name, data in cases:
                result = core.verify(data, base/name, timeout=120)
                package = library.register(base/name, base/'source', name=name, timeout=120)
                library.export(package['id'], base/(name+'.json'), base/'source')
                imported = library.import_package(base/(name+'.json'), base/'destination', timeout=120)
                self.assertEqual(imported, package)
                self.assertEqual(library.read_evidence_json(imported, 'result.json'), result)
                self.assertEqual(result['numerical']['diagnostic'], 'backend_unavailable')
                self.assertEqual(result['status'], 'proved' if name == 'Gamma' else 'unresolved')
                if name == 'Cross':
                    self.assertFalse(result['full_bessel_proof'])
                    self.assertTrue(result['conditional_lean']['accepted'])

    def test_derived_external_package_reverifies_current_dependencies(self):
        with tempfile.TemporaryDirectory(prefix='research-derived-lean-') as temporary, \
             patch('special_function_agent.real_numeric.importlib.import_module', side_effect=without_mpmath):
            base = Path(temporary)
            core.verify(request(), base/'leaf-run', timeout=120)
            leaf = library.register(base/'leaf-run', base/'source', name='Gamma-leaf', timeout=120)
            data = derived_request(leaf, 'steps')
            result = core.verify(data, base/'derived-run', timeout=120)
            self.assertEqual(result['status'], 'proved', result)
            derived = library.register(base/'derived-run', base/'source', name='Gamma-derived', timeout=120)
            external = base/'derived.json'
            library.export(derived['id'], external, base/'source')
            before = external.read_bytes()
            source_before = snapshot(base/'source')
            updated_environment = {**core.environment(), 'acceptance-environment': 'explicit-reverification'}
            with patch('special_function_agent.real_special.environment', return_value=updated_environment), \
                 patch('special_function_agent.research_proof.environment', return_value=updated_environment):
                with self.assertRaisesRegex(core.InputError, 'environment'):
                    library.import_package(external, base/'destination', timeout=120)
                current = library.reverify_package(external, base/'destination', timeout=120)
            self.assertEqual(current['previous_id'], derived['id'])
            current_data = library.read_evidence_json(current['package'], 'request.json')
            self.assertEqual(current_data['lhs'], data['lhs'])
            self.assertEqual(current_data['rhs'], data['rhs'])
            self.assertEqual(current_data['assumptions'], data['assumptions'])
            child = current_data['proof']['lemmas'][0]
            self.assertNotEqual(child['id'], leaf['id'])
            self.assertEqual(current_data['proof']['steps'][0]['uses'][0]['lemma'], child['id'])
            self.assertEqual(library.read_evidence_json(current['package'], 'result.json')['status'], 'proved')
            self.assertEqual(len(library.list_entries(base/'destination')), 1)
            self.assertEqual(external.read_bytes(), before)
            self.assertEqual(snapshot(base/'source'), source_before)


if __name__ == '__main__':
    unittest.main()
