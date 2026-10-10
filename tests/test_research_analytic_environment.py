"""Optional analytic evidence binds its module without changing semantic identity."""
from contextlib import contextmanager
from copy import deepcopy
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from special_function_agent import core, defined_proof, real_special
from special_function_agent import research_functions as functions
from special_function_agent import research_function_library as library
from special_function_agent import research_proof
from special_function_agent import registry
from special_function_agent.archive import target_hash


MODULE = 'SpecialFunctionProofAgent/AnalyticDefinitions.lean'
SLUGS = ('exp-series', 'gaussian-primitive', 'linear-ivp')
# Synthetic acceptance is used only by bookkeeping boundary tests.
ACCEPTED = {'accepted': True, 'axioms': [],
            'stdout': "BESSEL_AUDIT_BEGIN\n'BesselAgentCandidate.target' does not depend on any axioms\nBESSEL_AUDIT_END\n"}
NUMERICAL = {'diagnostic': 'backend_unavailable'}


def example(slug, kind):
    return core.load_json(core.ROOT/'examples'/f'research-analytic-{slug}.{kind}.json')


def source_request(slug='exp-series'):
    data = example(slug, 'source.target')
    return {**data, 'proof': defined_proof.default_proof(data)}


def finite_request():
    return core.load_json(core.ROOT/'demo/defined-gamma-direct/request.json')


@contextmanager
def changed_analytic_module():
    """Change only the bytes observed by fingerprinting; never edit Lean sources."""
    original = Path.read_bytes

    def read(path):
        value = original(path)
        return value+b'\n-- simulated analytic revision\n' if path == core.ROOT/MODULE else value

    with patch.object(Path, 'read_bytes', read):
        yield


def lemma_package(directory, name='Analytic-source'):
    evidence = {name: (directory/name).read_text(encoding='utf-8') for name in
                ('request.json', 'result.json', 'certificate.lean', 'proof_attempt.lean', 'analysis.json')}
    package = {'schema_version': 1, 'name': name, 'source': None, 'original_input': None,
               'evidence': evidence,
               'manifest': {name: core._sha(text.encode()) for name, text in evidence.items()}}
    package['id'] = core._sha(json.dumps(package, ensure_ascii=False, sort_keys=True,
                                         separators=(',', ':'), allow_nan=False).encode())
    return package


def finite_research_target(package):
    x = {'op': 'var', 'name': 'x'}
    exponential = {'op': 'exp', 'arg': x}
    return {'schema_version': 2, 'variables': {'x': 'real'}, 'assumptions': [],
            'lhs': {'op': 'add', 'args': [exponential, exponential]},
            'rhs': {'op': 'mul', 'args': [{'op': 'int', 'value': 2}, exponential]},
            'proof': {'mode': 'direct', 'recipe': 'research', 'lemmas': [package],
                      'uses': [{'lemma': package['id'], 'arguments': {'x': x}, 'reverse': False}]}}


class ResearchAnalyticEnvironmentTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='sf-analytic-environment-')
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)

    def verified_fixture(self, request, name):
        """Save a synthetic accepted run to exercise evidence checks without Lean."""
        output = self.root/name
        with patch.object(real_special, '_run_lean', return_value=ACCEPTED), \
             patch('special_function_agent.real_numeric.diagnose', return_value=NUMERICAL):
            result = core.verify(request, output)
        self.assertEqual(result['status'], 'proved', result)
        return output, result

    def test_published_base_evidence_and_finite_certificates_remain_compatible(self):
        baseline = core.environment()
        self.assertNotIn(MODULE, baseline)
        checked = 0
        for output in sorted((core.ROOT/'demo').iterdir()):
            if not (output/'result.json').is_file():
                continue
            request = core.load_json(output/'request.json')
            if functions.uses_analytic(request):
                continue
            with self.subTest(demo=output.name):
                self.assertEqual(core.load_json(output/'result.json')['environment'], baseline)
            checked += 1
        self.assertGreaterEqual(checked, 117)
        for route in ('defined-gamma-direct', 'defined-gamma-steps',
                      'defined-gamma-tail-direct', 'defined-gamma-tail-steps'):
            output = core.ROOT/'demo'/route
            request = core.load_json(output/'request.json')
            with self.subTest(route=route):
                self.assertEqual(core.render_lean(request).encode(), (output/'certificate.lean').read_bytes())
                self.assertEqual(defined_proof.conventions(request),
                                 core.load_json(output/'result.json')['conventions'])
                for snapshot in request['definitions']:
                    self.assertEqual(functions.make_definition({k: v for k, v in snapshot.items() if k != 'id'}), snapshot)

    def test_module_revision_preserves_all_semantic_ids_targets_and_conventions(self):
        baseline = core.environment()
        finite = finite_request()
        finite_source = core.render_lean(finite)
        for slug in SLUGS:
            raw = example(slug, 'definition')
            snapshot = functions.make_definition(raw)
            request = source_request(slug)
            before = deepcopy(request)
            environment = functions.environment(request)
            identity = target_hash(request)
            conventions = defined_proof.conventions(request)
            declaration = functions.render_definition(snapshot)
            with self.subTest(slug=slug), changed_analytic_module():
                changed = functions.environment(request)
                self.assertNotEqual(changed[MODULE], environment[MODULE])
                self.assertEqual({k: v for k, v in changed.items() if k != MODULE}, baseline)
                self.assertEqual(core.environment(), baseline)
                self.assertEqual(functions.make_definition(raw), snapshot)
                self.assertEqual(target_hash(request), identity)
                self.assertEqual(defined_proof.conventions(request), conventions)
                self.assertEqual(functions.render_definition(snapshot), declaration)
                self.assertEqual(functions.environment(finite), baseline)
                self.assertEqual(core.render_lean(finite), finite_source)
            self.assertEqual(request, before)

    def test_analytic_conventions_preserve_shared_registry_and_previous_results(self):
        baseline = deepcopy(registry.CONVENTIONS)
        first = functions.definition_conventions(functions.make_definition(example('exp-series', 'definition')))
        first_before = deepcopy(first)
        functions.definition_conventions(functions.make_definition(example('linear-ivp', 'definition')))
        self.assertEqual(registry.CONVENTIONS, baseline)
        self.assertEqual(first, first_before)
        self.assertIn('analytic_definitions', first)

    def test_stale_analytic_packages_reject_selection_and_import_before_lean(self):
        packages = []
        with patch.object(core, '_run_lean', return_value=ACCEPTED):
            for slug in SLUGS:
                packages.append(library.register(example(slug, 'definition'), self.root/'library'))
            raw = core.load_json(core.ROOT/'examples/research-function-shifted-gamma.definition.json')
            finite = library.register(raw, self.root/'library')
        with changed_analytic_module(), patch.object(core, '_run_lean') as runner:
            for package in packages:
                stored = self.root/'library/functions'/(package['id']+'.json')
                old_bytes = stored.read_bytes()
                with self.subTest(name=package['definition']['name']):
                    self.assertEqual(library.load(package['id'], self.root/'library'), package)
                    with self.assertRaisesRegex(core.InputError, 'environment'):
                        library.definitions([package])
                    with self.assertRaisesRegex(core.InputError, 'environment'):
                        library.import_package(stored, self.root/'imported')
                    self.assertEqual(stored.read_bytes(), old_bytes)
            self.assertEqual(library.definitions([finite]), [finite['definition']])
            runner.assert_not_called()
        self.assertFalse((self.root/'imported').exists())

    def test_explicit_reverification_appends_package_and_preserves_old_bytes_and_meaning(self):
        root = self.root/'library'
        with patch.object(core, '_run_lean', return_value=ACCEPTED):
            package = library.register(example('linear-ivp', 'definition'), root,
                                       source='fixed IVP', original_input="y'=rate*y; y(0)=initial")
        stored = root/'functions'/(package['id']+'.json')
        old_bytes = stored.read_bytes()
        generated = []

        def check(path, timeout):
            generated.append(path.read_text(encoding='utf-8'))
            return ACCEPTED

        with changed_analytic_module(), patch.object(core, '_run_lean', side_effect=check) as runner:
            updated = library.reverify(package['id'], root)
            fresh = updated['package']
            self.assertEqual(updated['previous_id'], package['id'])
            self.assertNotEqual(fresh['id'], package['id'])
            self.assertEqual(fresh['definition'], package['definition'])
            self.assertEqual(fresh['conventions'], package['conventions'])
            self.assertEqual(fresh['source'], package['source'])
            self.assertEqual(fresh['original_input'], package['original_input'])
            self.assertNotEqual(fresh['environment'][MODULE], package['environment'][MODULE])
            self.assertEqual(library.definitions([fresh]), [package['definition']])
            self.assertEqual(generated, [functions.render_definition(package['definition'])])
            runner.assert_called_once()
        self.assertEqual(stored.read_bytes(), old_bytes)
        self.assertEqual({p.stem for p in (root/'functions').glob('*.json')}, {package['id'], fresh['id']})

    def test_saved_analytic_replay_rejects_revision_while_finite_replay_continues(self):
        finite, _ = self.verified_fixture(finite_request(), 'finite')
        outputs = [self.verified_fixture(source_request(slug), slug)[0] for slug in SLUGS]
        old_bytes = {path: path.read_bytes() for output in outputs for path in output.iterdir() if path.is_file()}
        with changed_analytic_module(), patch.object(real_special, '_run_lean', return_value=ACCEPTED) as runner:
            for output in outputs:
                with self.subTest(output=output.name), self.assertRaisesRegex(core.InputError, 'environment'):
                    core.replay(output)
            runner.assert_not_called()
            self.assertTrue(core.replay(finite)['replayed'])
            runner.assert_called_once()
        self.assertEqual({path: path.read_bytes() for path in old_bytes}, old_bytes)

    def test_analytic_source_dependency_survives_finite_and_nested_research_targets(self):
        source, _ = self.verified_fixture(source_request(), 'source')
        package = lemma_package(source)
        request = finite_research_target(package)
        self.assertFalse(functions.contains(request))
        self.assertTrue(functions.uses_analytic(request))
        self.assertIn(MODULE, functions.environment(request))
        generated = research_proof.render(request)
        self.assertIn('import SpecialFunctionProofAgent.AnalyticDefinitions\n', generated)
        self.assertIn('namespace ResearchLemma_'+package['id'], generated)
        derived, result = self.verified_fixture(request, 'derived')
        self.assertIn(MODULE, result['environment'])
        nested = finite_research_target(lemma_package(derived, 'Finite-derived'))
        self.assertFalse(functions.contains(nested))
        self.assertTrue(functions.uses_analytic(nested))
        self.assertIn(MODULE, functions.environment(nested))
        self.assertEqual(len(research_proof.inspect_dependencies(nested)), 2)
        with changed_analytic_module(), patch.object(real_special, '_run_lean') as runner:
            for data in (request, nested):
                with self.subTest(nested=data is nested), self.assertRaisesRegex(core.InputError, 'environment'):
                    research_proof.render(data)
            with self.assertRaisesRegex(core.InputError, 'environment'):
                core.replay(derived)
            runner.assert_not_called()


@unittest.skipUnless(os.environ.get('SF_RUN_LEAN_TESTS') == '1' or os.environ.get('BESSEL_RUN_LEAN_TESTS') == '1',
                     'Enable Lean for analytic-source reuse across a finite target.')
class ResearchAnalyticEnvironmentLeanTests(unittest.TestCase):
    def test_real_source_lemma_finite_target_and_replay_keep_optional_module(self):
        with tempfile.TemporaryDirectory(prefix='sf-analytic-environment-lean-') as temporary, \
             patch('special_function_agent.real_numeric.diagnose', return_value=NUMERICAL):
            root = Path(temporary)
            source = core.verify(source_request(), root/'source', timeout=120)
            self.assertEqual(source['status'], 'proved', source)
            request = finite_research_target(lemma_package(root/'source'))
            result = core.verify(request, root/'finite', timeout=120)
            self.assertEqual(result['status'], 'proved', result)
            self.assertTrue(result['full_function_proof'])
            self.assertIn(MODULE, result['environment'])
            self.assertNotEqual(target_hash(request), target_hash(source_request()))
            self.assertIn('import SpecialFunctionProofAgent.AnalyticDefinitions\n',
                          (root/'finite/certificate.lean').read_text())
            self.assertTrue(core.replay(root/'finite', timeout=120)['replayed'])


if __name__ == '__main__':
    unittest.main()
