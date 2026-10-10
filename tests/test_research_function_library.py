"""Private definition packages preserve meaning and execute regenerated Lean only."""
from copy import deepcopy
import hashlib
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from special_function_agent import core, research_library
from special_function_agent import research_function_library as library
from special_function_agent.research_functions import make_definition, render_definition


ACCEPTED = {'accepted': True, 'axioms': [],
            'stdout': "BESSEL_AUDIT_BEGIN\n'BesselAgentCandidate.target' does not depend on any axioms\nBESSEL_AUDIT_END\n"}


def raw_definition(name='ShiftedGamma', offset=1):
    return {'schema_version': 1, 'name': name, 'parameters': {'u': 'real'},
            'body': {'op': 'gamma', 'arg': {'op': 'add', 'args': [
                {'op': 'var', 'name': 'u'}, {'op': 'int', 'value': offset}]}},
            'definitions': []}


def dependent_definition(base):
    return {'schema_version': 1, 'name': 'DoubledGamma', 'parameters': {'v': 'real'},
            'body': {'op': 'mul', 'args': [{'op': 'int', 'value': 2},
                {'op': 'defined', 'function': base['id'],
                 'arguments': {'u': {'op': 'var', 'name': 'v'}}}]},
            'definitions': [base]}


def encoded(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(',', ':'),
                      allow_nan=False).encode('utf-8')


def repack(package):
    package = deepcopy(package)
    package.pop('id', None)
    package['id'] = hashlib.sha256(encoded(package)).hexdigest()
    return package


class ResearchFunctionLibraryTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='research-function-library-test-')
        self.addCleanup(temporary.cleanup)
        self.base = Path(temporary.name).resolve()
        self.root = self.base/'research'

    def package(self, raw=None, **metadata):
        return library.register(raw or raw_definition(), self.root, **metadata)

    def external(self, package, name='external.json'):
        path = self.base/name
        path.write_bytes(encoded(package)+b'\n')
        return path

    def stored(self, package):
        return self.root/'functions'/(package['id']+'.json')

    def test_default_root_environment_isolation_and_repository_boundary(self):
        with patch.dict(os.environ, {'SPECIAL_FUNCTION_ARCHIVE_DIR': str(self.base/'archive'),
                                     'BESSEL_ARCHIVE_DIR': str(self.base/'legacy')}, clear=True), \
             patch('pathlib.Path.home', return_value=self.base):
            expected = self.base/'SpecialFunctionProofAgentData/research/functions'
            self.assertEqual(library.resolve_root(), expected)
            self.assertEqual(library.list_entries(), [])
            self.assertFalse(expected.exists())
            with patch.dict(os.environ, {'SPECIAL_FUNCTION_RESEARCH_DIR': str(self.root)}):
                self.assertEqual(library.resolve_root(), self.root/'functions')
                self.assertEqual(library.resolve_root(self.base/'explicit'), self.base/'explicit/functions')
        alias = self.base/'repo-alias'
        alias.symlink_to(core.ROOT, target_is_directory=True)
        for root in (core.ROOT, core.ROOT/'research', alias/'research'):
            with self.subTest(root=root), self.assertRaises(core.InputError):
                library.resolve_root(root)

    def test_register_export_import_checks_only_generated_source_and_keeps_bytes(self):
        sources = []

        def check(path, timeout):
            self.assertEqual(timeout, 120)
            sources.append((path, path.read_text(encoding='utf-8')))
            return ACCEPTED

        raw = raw_definition()
        raw_before = deepcopy(raw)
        with patch.object(core, '_run_lean', side_effect=check) as lean:
            package = self.package(raw, source='#eval metadata only', original_input='Gamma(u+1)', timeout=120)
            stored = self.stored(package)
            before = stored.read_bytes()
            self.assertEqual(package['verification']['status'], 'defined')
            self.assertEqual(library.load(package['id'], self.root), package)
            self.assertEqual(library.list_entries(self.root), [package])
            self.assertEqual(research_library.list_entries(self.root), [])
            destination = self.base/'shared/chosen.json'
            exported = library.export(package['id'], destination, self.root)
            self.assertEqual(exported, {'id': package['id'], 'definition_id': package['definition']['id'],
                                        'path': str(destination)})
            second = self.base/'second'
            self.assertEqual(library.import_package(destination, second, timeout=120), package)
            self.assertEqual(library.import_package(destination, second, timeout=120), package)
            self.assertEqual(lean.call_count, 3)
            with self.assertRaises(core.InputError):
                library.export(package['id'], destination, self.root)
            self.assertEqual(stored.read_bytes(), before)
            self.assertEqual(destination.read_bytes(), before)
            self.assertEqual((second/'functions'/stored.name).read_bytes(), before)
            self.assertEqual(stored.stat().st_mode & 0o777, 0o600)
        self.assertEqual(raw, raw_before)
        self.assertEqual(len({path.parent for path, _ in sources}), 3)
        self.assertTrue(all(source == render_definition(package['definition']) for _, source in sources))
        self.assertTrue(all('#eval metadata only' not in source for _, source in sources))

    def test_pure_validation_preserves_old_environment_without_execution(self):
        with patch.object(core, '_run_lean', return_value=ACCEPTED):
            package = self.package()
        package['environment'] = {'old': 'environment'}
        package = repack(package)
        with patch.object(core, 'environment', side_effect=AssertionError('current environment lookup')), \
             patch.object(core, '_run_lean', side_effect=AssertionError('Lean execution')):
            self.assertIs(library.validate_package(package), package)

    def test_strict_package_fields_status_axioms_and_content_hash(self):
        with patch.object(core, '_run_lean', return_value=ACCEPTED):
            package = self.package()
        mutations = [
            lambda p: p.update(schema_version=True),
            lambda p: p.update(kind='theorem'),
            lambda p: p.update(status='proved'),
            lambda p: p.update(environment={}),
            lambda p: p.update(environment={'x': 1}),
            lambda p: p.update(conventions=[]),
            lambda p: p.update(source=3),
            lambda p: p.update(certificate=3),
            lambda p: p['verification'].update(status='proved'),
            lambda p: p['verification'].update(accepted=1),
            lambda p: p['verification'].update(accepted=False),
            lambda p: p['verification'].update(axioms=['propext']),
            lambda p: p['verification'].update(stderr='extra'),
            lambda p: p['verification'].update(stdout="BESSEL_AUDIT_BEGIN\n'BesselAgentCandidate.target' depends on axioms: [sorryAx]\nBESSEL_AUDIT_END"),
            lambda p: p['definition']['body']['arg']['args'][1].update(value=2),
        ]
        for mutate in mutations:
            changed = deepcopy(package)
            mutate(changed)
            with self.subTest(value=changed), self.assertRaises(core.InputError):
                library.validate_package(repack(changed))
        for identifier in ('../chosen', 'f'*63, 'F'*64, [], None):
            with self.subTest(identifier=identifier), self.assertRaises(core.InputError):
                library.load(identifier, self.root)
        changed = deepcopy(package)
        changed['source'] = 'changed without updating hash'
        with self.assertRaises(core.InputError):
            library.validate_package(changed)

    def test_strict_json_duplicate_nonfinite_utf8_and_size_limits(self):
        with patch.object(core, '_run_lean', return_value=ACCEPTED):
            package = self.package()
        payload = encoded(package)
        variants = [payload[:-1]+b',"kind":"function_definition"}',
                    payload.replace(b'"source":null', b'"source":NaN'),
                    payload.replace(b'"source":null', b'"source":1e999'),
                    payload.replace(b'"source":null', b'"source":"\\ud800"'),
                    b'\xff', b' '* (research_library.MAX_PACKAGE_BYTES+1)]
        with patch.object(core, '_run_lean') as lean:
            for index, payload in enumerate(variants):
                path = self.base/f'invalid-{index}.json'
                path.write_bytes(payload)
                with self.subTest(index=index), self.assertRaises(core.InputError):
                    library.import_package(path, self.base/'imported')
            with self.assertRaises(core.InputError):
                self.package(source='x'*research_library.MAX_PACKAGE_BYTES)
            with self.assertRaises(core.InputError):
                self.package(original_input='\ud800')
            lean.assert_not_called()
        self.assertFalse((self.base/'imported').exists())

    def test_symlink_and_export_repository_boundaries(self):
        with patch.object(core, '_run_lean', return_value=ACCEPTED):
            package = self.package()
        external = self.external(package)
        file_alias = self.base/'file-alias.json'
        file_alias.symlink_to(external)
        root_alias = self.base/'root-alias'
        root_alias.symlink_to(self.root, target_is_directory=True)
        other = self.base/'other'
        other.mkdir()
        (other/'functions').symlink_to(self.root/'functions', target_is_directory=True)
        repo_alias = self.base/'repo'
        repo_alias.symlink_to(core.ROOT, target_is_directory=True)
        calls = [lambda: library.import_package(file_alias, self.base/'imported'),
                 lambda: library.reverify_package(file_alias, self.base/'imported'),
                 lambda: library.resolve_root(root_alias), lambda: library.resolve_root(other),
                 lambda: library.export(package['id'], file_alias, self.root),
                 lambda: library.export(package['id'], core.ROOT/'private-definition.json', self.root),
                 lambda: library.export(package['id'], repo_alias/'private-definition.json', self.root)]
        with patch.object(core, '_run_lean') as lean:
            for index, call in enumerate(calls):
                with self.subTest(index=index), self.assertRaises(core.InputError):
                    call()
            lean.assert_not_called()
        self.stored(package).unlink()
        self.stored(package).symlink_to(external)
        with self.assertRaises(core.InputError):
            library.load(package['id'], self.root)

    def test_wrong_filename_and_unknown_library_entries_are_rejected(self):
        with patch.object(core, '_run_lean', return_value=ACCEPTED):
            package = self.package()
        wrong = self.root/'functions'/('f'*64+'.json')
        wrong.write_bytes(self.stored(package).read_bytes())
        with self.assertRaises(core.InputError):
            library.load('f'*64, self.root)
        wrong.unlink()
        unexpected = self.root/'functions/notes.txt'
        unexpected.write_text('not a package')
        with self.assertRaises(core.InputError):
            library.list_entries(self.root)

    def test_changed_raw_lean_is_rejected_before_import_or_selection_execution(self):
        with patch.object(core, '_run_lean', return_value=ACCEPTED):
            package = self.package()
        original_path = self.stored(package)
        original = original_path.read_bytes()
        package['certificate'] = '#eval IO.println "untrusted external payload"\n'
        package = repack(package)
        external = self.external(package)
        with patch.object(core, '_run_lean') as lean:
            with self.assertRaises(core.InputError):
                library.import_package(external, self.base/'imported')
            with self.assertRaises(core.InputError):
                library.definitions([package])
            lean.assert_not_called()
        generated = []
        def check(path, timeout):
            generated.append(path.read_text(encoding='utf-8'))
            return ACCEPTED
        with patch.object(core, '_run_lean', side_effect=check):
            refreshed = library.reverify_package(external, self.base/'refreshed')
        self.assertEqual(refreshed['previous_id'], package['id'])
        self.assertEqual(refreshed['package']['definition'], package['definition'])
        self.assertEqual(generated, [render_definition(package['definition'])])
        self.assertEqual(external.read_bytes(), encoded(package)+b'\n')
        self.assertEqual(original_path.read_bytes(), original)

    def test_environment_change_requires_explicit_reverification_and_keeps_semantic_id(self):
        with patch.object(core, '_run_lean', return_value=ACCEPTED):
            package = self.package(source='https://example.org/definition', original_input='Gamma(u+1)')
        old_bytes = self.stored(package).read_bytes()
        external = self.external(package)
        external_before = external.read_bytes()
        updated_environment = {**package['environment'], 'future-environment': 'changed'}
        with patch.object(core, 'environment', return_value=updated_environment), \
             patch.object(core, '_run_lean', return_value=ACCEPTED) as lean:
            self.assertEqual(library.load(package['id'], self.root), package)
            self.assertEqual(library.list_entries(self.root), [package])
            with self.assertRaises(core.InputError):
                library.import_package(external, self.base/'imported')
            with self.assertRaises(core.InputError):
                library.definitions([package])
            lean.assert_not_called()
            refreshed = library.reverify(package['id'], self.root)
            imported = library.reverify_package(external, self.base/'imported')
            self.assertEqual(lean.call_count, 2)
            self.assertEqual(imported, refreshed)
            updated = refreshed['package']
            self.assertEqual(refreshed['previous_id'], package['id'])
            self.assertNotEqual(updated['id'], package['id'])
            self.assertEqual(updated['definition'], package['definition'])
            self.assertEqual(updated['source'], package['source'])
            self.assertEqual(updated['original_input'], package['original_input'])
            self.assertEqual(library.definitions([updated]), [package['definition']])
            self.assertEqual(len(library.list_entries(self.root)), 2)
        self.assertEqual(self.stored(package).read_bytes(), old_bytes)
        self.assertEqual(external.read_bytes(), external_before)

    def test_conventions_mismatch_and_environment_race_leave_no_record(self):
        with patch.object(core, '_run_lean', return_value=ACCEPTED):
            package = self.package()
        package['conventions'] = {'wrong': 'normalization'}
        package = repack(package)
        with patch.object(core, '_run_lean') as lean:
            with self.assertRaises(core.InputError):
                library.import_package(self.external(package), self.base/'imported')
            lean.assert_not_called()
        race_root = self.base/'race'
        with patch.object(core, 'environment', side_effect=[{'env': 'before'}, {'env': 'after'}]), \
             patch.object(core, '_run_lean', return_value=ACCEPTED):
            with self.assertRaises(core.InputError):
                library.register(raw_definition(), race_root)
        self.assertFalse(race_root.exists())

    def test_definition_dependencies_are_embedded_and_selection_returns_independent_copies(self):
        with patch.object(core, '_run_lean', return_value=ACCEPTED):
            base = self.package()
            parent = self.package(dependent_definition(base['definition']))
        selected = library.definitions([parent])
        self.assertEqual(selected, [parent['definition']])
        self.assertEqual(selected[0]['definitions'], [base['definition']])
        selected[0]['definitions'][0]['body'] = {'op': 'int', 'value': 1}
        self.assertEqual(library.load(parent['id'], self.root), parent)
        external = self.base/'dependency.json'
        library.export(parent['id'], external, self.root)
        with patch.object(core, '_run_lean', return_value=ACCEPTED):
            imported = library.import_package(external, self.base/'second')
        self.assertEqual(library.list_entries(self.base/'second'), [imported])
        self.assertIn('ResearchFunction_'+base['definition']['id'], imported['certificate'])
        for invalid in ([], [parent, parent], {}, [parent]*13):
            with self.subTest(invalid=invalid), self.assertRaises(core.InputError):
                library.definitions(invalid)

    def test_same_name_different_definitions_use_explicit_distinct_ids(self):
        with patch.object(core, '_run_lean', return_value=ACCEPTED):
            first = self.package()
            second = self.package(raw_definition(offset=2))
        self.assertNotEqual(first['id'], second['id'])
        self.assertNotEqual(first['definition']['id'], second['definition']['id'])
        self.assertEqual(first['definition']['name'], second['definition']['name'])
        self.assertEqual(len(library.list_entries(self.root)), 2)
        with self.assertRaises(core.InputError):
            library.load(first['definition']['name'], self.root)
        self.assertEqual(library.definitions([second]), [second['definition']])

    def test_definition_shape_and_failed_lean_do_not_create_records(self):
        invalids = []
        for name in ('../unsafe', 'Bad Name', 'sorry'):
            invalids.append(raw_definition(name))
        invalid = raw_definition()
        invalid['parameters'] = {'u': 'nat'}
        invalids.append(invalid)
        invalid = raw_definition()
        invalid['body'] = {'op': 'deriv', 'var': 'u', 'arg': {'op': 'var', 'name': 'u'}}
        invalids.append(invalid)
        invalid = raw_definition()
        invalid['certificate'] = 'arbitrary Lean'
        invalids.append(invalid)
        with patch.object(core, '_run_lean') as lean:
            for invalid in invalids:
                with self.subTest(invalid=invalid), self.assertRaises(core.InputError):
                    self.package(invalid)
            lean.assert_not_called()
        for result in ({'accepted': False, 'reason': 'lean_rejected'},
                       {**ACCEPTED, 'axioms': ['sorryAx']}, {**ACCEPTED, 'stdout': ''}):
            with patch.object(core, '_run_lean', return_value=result), self.assertRaises(core.InputError):
                self.package()
        self.assertFalse(self.root.exists())


@unittest.skipUnless(os.environ.get('SF_RUN_LEAN_TESTS') == '1', 'Set SF_RUN_LEAN_TESTS=1 for real Lean acceptance.')
class ResearchFunctionLibraryLeanTests(unittest.TestCase):
    def test_real_lean_register_export_import_and_reverify_dependency_closure(self):
        with tempfile.TemporaryDirectory(prefix='research-function-library-lean-') as temporary:
            base = Path(temporary)
            root, second = base/'research', base/'second'
            definition = dependent_definition(make_definition(raw_definition()))
            package = library.register(definition, root, source='Explicit finite composition', timeout=120)
            stored = root/'functions'/(package['id']+'.json')
            original = stored.read_bytes()
            self.assertEqual(package['verification']['status'], 'defined')
            self.assertTrue(package['verification']['accepted'])
            self.assertLessEqual(set(package['verification']['axioms']), core.ALLOWED_AXIOMS)
            external = base/'chosen.json'
            library.export(package['id'], external, root)
            self.assertEqual(library.import_package(external, second, timeout=120), package)
            changed = {**package['environment'], 'migration-test': 'current'}
            with patch.object(core, 'environment', return_value=changed):
                migrated = library.reverify_package(external, second, timeout=120)
                self.assertNotEqual(migrated['package']['id'], package['id'])
                self.assertEqual(migrated['package']['definition'], package['definition'])
                self.assertEqual(library.definitions([migrated['package']]), [package['definition']])
            self.assertEqual(migrated['previous_id'], package['id'])
            self.assertEqual(stored.read_bytes(), original)
            self.assertEqual(external.read_bytes(), original)
            self.assertEqual((second/'functions'/stored.name).read_bytes(), original)


if __name__ == '__main__':
    unittest.main()
