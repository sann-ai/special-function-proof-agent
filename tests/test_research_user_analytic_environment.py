"""User-expression semantics stay fixed while their optional foundation is rechecked."""
from contextlib import contextmanager
from copy import deepcopy
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from special_function_agent import core, defined_proof, research_functions as functions
from special_function_agent import research_function_library as library
from special_function_agent.archive import target_hash

MODULE = 'SpecialFunctionProofAgent/UserAnalyticDefinitions.lean'


def example(slug, kind):
    return core.load_json(core.ROOT/'examples'/f'research-user-{slug}.{kind}.json')


@contextmanager
def changed_module():
    read = Path.read_bytes
    def changed(path):
        result = read(path)
        return result+b'\n-- simulated revision\n' if path == core.ROOT/MODULE else result
    with patch.object(Path, 'read_bytes', changed): yield


class UserAnalyticEnvironmentTests(unittest.TestCase):
    def test_module_hash_is_scoped_and_preserves_old_evidence(self):
        baseline = core.environment()
        self.assertNotIn(MODULE, baseline)
        checked = 0
        for output in (core.ROOT/'demo').iterdir():
            if not (output/'result.json').exists(): continue
            request = core.load_json(output/'request.json')
            if functions.uses_user_analytic(request) or functions.uses_advanced_analytic(request): continue
            with self.subTest(output=output.name):
                self.assertEqual(functions.environment(request), core.load_json(output/'result.json')['environment'])
                self.assertNotIn(MODULE, functions.environment(request))
            checked += 1
        self.assertGreaterEqual(checked, 129)

    def test_revision_changes_environment_only_for_each_user_class(self):
        for slug in ('series', 'integral', 'ode'):
            raw, target = example(slug, 'definition'), example(slug, 'source.target')
            snapshot = functions.make_definition(raw)
            before = deepcopy(target)
            env, identity = functions.environment(target), target_hash(target)
            conventions = defined_proof.conventions(target)
            source = functions.render_definition(snapshot)
            with self.subTest(slug=slug), changed_module():
                fresh = functions.environment(target)
                self.assertNotEqual(fresh[MODULE], env[MODULE])
                self.assertEqual({k:v for k,v in fresh.items() if k != MODULE},
                                 {k:v for k,v in env.items() if k != MODULE})
                self.assertEqual(functions.make_definition(raw), snapshot)
                self.assertEqual(target_hash(target), identity)
                self.assertEqual(defined_proof.conventions(target), conventions)
                self.assertEqual(functions.render_definition(snapshot), source)
            self.assertEqual(target, before)

    def test_source_lemma_dependency_keeps_user_module_hash(self):
        import json
        target = example('series', 'source.target')
        dependency = {'proof': {'lemmas': [{'evidence': {'request.json': json.dumps(target)}}]}}
        self.assertTrue(functions.uses_user_analytic(dependency))
        self.assertEqual(functions.environment(dependency), functions.environment(target))


@unittest.skipUnless(os.environ.get('SF_RUN_LEAN_TESTS') == '1', 'Set SF_RUN_LEAN_TESTS=1 for Lean checks.')
class UserAnalyticEnvironmentLeanTests(unittest.TestCase):
    def test_degree_twelve_primitive_and_zero_series_contracts(self):
        raw = {'schema_version': 1, 'name': 'TwelfthArea', 'parameters': {'x': 'real'},
               'body': {'op': 'integral_definition', 'var': 't',
                        'integrand': {'op': 'pow', 'base': {'op': 'var', 'name': 't'}, 'exponent': 12},
                        'lower': {'op': 'int', 'value': 0}, 'upper': {'op': 'var', 'name': 'x'}},
               'definitions': []}
        with tempfile.TemporaryDirectory(prefix='sf-user-degree-boundary-') as directory:
            package = library.register(raw, Path(directory), timeout=90)
            self.assertIn('IntervalIntegrable', package['certificate'])
            raw['name'] = 'ZeroSeries'
            raw['body'] = {'op': 'series_definition', 'index': 'k', 'term': {'op': 'int', 'value': 0}}
            package = library.register(raw, Path(directory), timeout=90)
            self.assertIn('HasSum', package['certificate'])

    def test_reverification_appends_new_environment_and_preserves_original_package(self):
        with tempfile.TemporaryDirectory(prefix='sf-user-environment-') as directory:
            root = Path(directory)
            package = library.register(example('ode', 'definition'), root, timeout=90)
            path = root/'functions'/(package['id']+'.json')
            original = path.read_bytes()
            with changed_module():
                with self.assertRaisesRegex(core.InputError, 'environment'):
                    library.definitions([package])
                with self.assertRaisesRegex(core.InputError, 'environment'):
                    library.import_package(path, root/'imported')
                updated = library.reverify(package['id'], root, timeout=90)['package']
                self.assertNotEqual(updated['id'], package['id'])
                self.assertEqual(updated['definition'], package['definition'])
                self.assertEqual(updated['conventions'], package['conventions'])
                self.assertEqual(library.definitions([updated]), [package['definition']])
            self.assertEqual(path.read_bytes(), original)
            self.assertEqual(len(list((root/'functions').glob('*.json'))), 2)


if __name__ == '__main__': unittest.main()
