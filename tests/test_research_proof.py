"""Closed research plans preserve domains, binders, evidence, and Lean assumptions."""
from copy import deepcopy
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from special_function_agent import core, real_bessel, real_special, research_proof as research
from special_function_agent.archive import target_hash
from special_function_agent.parser import parse_identity
from special_function_agent.registry import conventions


GAMMA = 'Gamma(x+1)=x*Gamma(x);x>0'
GAMMA_TWO = 'Gamma(x+2)=(x+1)*x*Gamma(x);x>0'


def repack(package):
    package = deepcopy(package)
    package['manifest'] = {name: core._sha(text.encode()) for name, text in package['evidence'].items()}
    package.pop('id', None)
    package['id'] = core._sha(json.dumps(package, ensure_ascii=False, sort_keys=True,
                                         separators=(',', ':'), allow_nan=False).encode())
    return package


def package_from_run(directory, name='Gamma-recurrence'):
    evidence = {filename: (directory/filename).read_text() for filename in
                ('request.json', 'result.json', 'certificate.lean', 'proof_attempt.lean', 'analysis.json')
                if (directory/filename).exists()}
    return repack({'schema_version': 1, 'name': name, 'source': None,
                   'original_input': None, 'evidence': evidence, 'manifest': {}})


def gamma_package():
    return package_from_run(core.ROOT/'demo/gamma-direct')


def use(package, argument, reverse=False):
    return {'lemma': package['id'], 'arguments': {'x': argument}, 'reverse': reverse}


def gamma_plan(package, route='direct', text=GAMMA_TWO):
    target = parse_identity(text)
    x = {'op': 'var', 'name': 'x'}
    plus_one = {'op': 'add', 'args': [x, {'op': 'int', 'value': 1}]}
    uses = [use(package, plus_one), use(package, x)]
    if route == 'direct':
        proof = {'mode': route, 'recipe': 'research', 'uses': uses, 'lemmas': [package]}
    else:
        normalized = parse_identity('Gamma((x+1)+1)=Gamma(x+2);x>0')['lhs']
        middle = parse_identity('Gamma(x+2)=(x+1)*Gamma(x+1);x>0')['rhs']
        endpoints = [(normalized, middle), (middle, target['rhs'])]
        first = {'before': target['lhs'], 'after': normalized, 'recipe': 'ring', 'uses': [],
                 'reason': '引数を漸化式に合う形に整理する。', 'conditions': []}
        proof = {'mode': route, 'lemmas': [package], 'steps': [first]+[
            {'before': lhs, 'after': rhs, 'recipe': 'research', 'uses': [item],
             'reason': '正の実引数で保存済み漸化式を適用する。', 'conditions': ['x > 0']}
            for (lhs, rhs), item in zip(endpoints, uses)]}
    return {**target, 'proof': proof}


def edit_result(package, edit):
    changed = deepcopy(package)
    result = json.loads(changed['evidence']['result.json'])
    edit(result)
    changed['evidence']['result.json'] = json.dumps(result)
    return repack(changed)


def boundary_fixture(data, name='Boundary-fixture'):
    """Synthetic acceptance metadata for validator tests; never a Lean acceptance claim."""
    source = real_special.render(data)
    request_text = json.dumps(data, ensure_ascii=False, indent=2)+'\n'
    accepted = json.loads(gamma_package()['evidence']['result.json'])['attempts'][-1]
    result = {'status': 'proved', 'full_function_proof': True, 'certificate_kind': 'proof',
              'environment': core.environment(), 'conventions': conventions(data),
              'request_sha256': core._sha(request_text.encode()), 'certificate_sha256': core._sha(source.encode()),
              'statement': real_bessel.display(data['lhs'])+' = '+real_bessel.display(data['rhs']),
              'conditions': real_bessel.labels(data), 'attempts': [accepted],
              'analysis': real_special.match_identity(data['lhs'], data['rhs'])}
    if research.is_research(data):
        result['formal_scope'] = research.FORMAL_SCOPE
        result['research_dependencies'] = research.inspect_dependencies(data)
        result['analysis'] = {'recipe': 'research', 'dependencies': result['research_dependencies']}
    if (real_special.cross_complete.complete_target(data) or real_special.bessel_y_integer.complete_target(data)
            or real_special.bessel_y_formal.contains(data)):
        result['full_bessel_proof'] = True
    return repack({'schema_version': 1, 'name': name, 'source': None, 'original_input': None,
                   'evidence': {'request.json': request_text, 'result.json': json.dumps(result),
                                'certificate.lean': source}, 'manifest': {}})


class ResearchProofBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.package = gamma_package()

    def test_both_routes_preserve_target_and_show_distinct_dependency_identity(self):
        original = parse_identity(GAMMA_TWO)
        for route in ('direct', 'steps'):
            data = gamma_plan(self.package, route)
            self.assertEqual({k: v for k, v in data.items() if k != 'proof'}, original)
            core.validate_request(data)
            source = research.render(data)
            self.assertIn('namespace ResearchLemma_'+self.package['id'], source)
            self.assertEqual(source.count('namespace BesselAgentCandidate'), 1)
            self.assertEqual(source.count('BESSEL_AUDIT_BEGIN'), 1)
            metadata, = research.inspect_dependencies(data)
            self.assertEqual(metadata, research.inspect_packages([self.package])[0])
            self.assertNotEqual(metadata['target_sha256'], target_hash(data))
            self.assertNotIn('sorry', source)
        algebra = gamma_plan(self.package)
        algebra['lhs'] = {'op': 'add', 'args': [{'op': 'var', 'name': 'x'}, {'op': 'var', 'name': 'x'}]}
        algebra['rhs'] = {'op': 'mul', 'args': [{'op': 'int', 'value': 2}, {'op': 'var', 'name': 'x'}]}
        self.assertEqual(core.render_lean(algebra), research.render(algebra))

    def test_proof_and_application_schema_reject_target_lean_and_condition_injection(self):
        for key in ('target', 'assumptions', 'lean'):
            data = gamma_plan(self.package)
            data['proof'][key] = 'untrusted'
            with self.subTest(key=key), self.assertRaises(core.InputError):
                research.render(data)
        for change in ('unknown_id', 'extra_argument', 'nonboolean_reverse', 'undeclared_variable'):
            data = gamma_plan(self.package)
            item = data['proof']['uses'][0]
            if change == 'unknown_id': item['lemma'] = '0'*64
            if change == 'extra_argument': item['arguments']['y'] = {'op': 'int', 'value': 1}
            if change == 'nonboolean_reverse': item['reverse'] = 1
            if change == 'undeclared_variable': item['arguments']['x'] = {'op': 'var', 'name': 'y'}
            with self.subTest(change=change), self.assertRaises(core.InputError):
                research.render(data)
        data = gamma_plan(self.package, 'steps')
        data['proof']['steps'][0]['conditions'].append('x > 1')
        with self.assertRaises(core.InputError): research.render(data)

    def test_nat_int_variables_and_binder_containing_arguments_are_explicitly_rejected(self):
        for kind in ('nat', 'int'):
            data = gamma_plan(self.package)
            data['variables']['n'] = kind
            with self.subTest(kind=kind), self.assertRaisesRegex(core.InputError, 'all free variables'):
                research.render(data)
        source = package_from_run(core.ROOT/'demo/hermite-h-derivative-direct', 'Hermite')
        with self.assertRaisesRegex(core.InputError, 'all free variables'):
            research.inspect_packages([source])
        for text in ('D_x(erf(x))=0;x real', 'int(0,x,exp(t),t)=0;x real'):
            data = gamma_plan(self.package)
            data['proof']['uses'][0]['arguments']['x'] = parse_identity(text)['lhs']
            with self.subTest(text=text), self.assertRaisesRegex(core.InputError, 'derivatives and integrals'):
                research.render(data)

    def test_missing_target_domains_and_unsafe_intermediate_domains_are_rejected(self):
        data = gamma_plan(self.package)
        data['assumptions'] = []
        with self.assertRaises(core.NeedsConditions): research.render(data)
        for middle in ({'op': 'gamma', 'arg': {'op': 'int', 'value': -1}},
                       {'op': 'div', 'args': [{'op': 'int', 'value': 1}, {'op': 'var', 'name': 'y'}]},
                       {'op': 'div', 'args': [{'op': 'int', 'value': 1}, {'op': 'int', 'value': 0}]}):
            data = gamma_plan(self.package, 'steps')
            data['variables']['y'] = 'real'
            data['proof']['steps'][0]['after'] = middle
            data['proof']['steps'][1]['before'] = middle
            with self.subTest(middle=middle), self.assertRaises(core.NeedsConditions): research.render(data)
        data = gamma_plan(self.package)
        data['proof']['uses'][0]['arguments']['x'] = middle
        with self.assertRaises(core.NeedsConditions): research.render(data)

    def test_rehashed_tampered_certificate_is_rejected_before_any_lean_execution(self):
        changed = deepcopy(self.package)
        changed['evidence']['certificate.lean'] = 'axiom fabricated : False\n'
        changed = repack(changed)
        with patch('special_function_agent.core._run_lean') as runner, self.assertRaises(core.InputError):
            research.render(gamma_plan(changed))
        runner.assert_not_called()
        changed = deepcopy(self.package)
        changed['evidence']['request.json'] += ' '
        with self.assertRaises(core.InputError): research.inspect_packages([changed])

    def test_full_status_environment_scope_and_standard_audit_are_required(self):
        updates = (
            lambda r: r.update(status='unresolved'),
            lambda r: r.update(full_function_proof=False),
            lambda r: r.update(full_bessel_proof=True),
            lambda r: r.update(certificate_kind='conditional'),
            lambda r: r.update(conditional_lean={'accepted': True}),
            lambda r: r.update(environment={}),
            lambda r: r.update(conventions={}),
            lambda r: r.update(formal_scope='invented scope'),
            lambda r: r.update(request_sha256='0'*64),
            lambda r: r.update(statement='False'),
            lambda r: r.update(conditions=[]),
            lambda r: r.update(attempts=[]),
            lambda r: r['attempts'][-1].update(axioms=['sorryAx']),
            lambda r: r['attempts'][-1].update(stdout=r['attempts'][-1]['stdout'].replace('propext', 'sorryAx')),
            lambda r: r.update(analysis={'recipe': 'changed'}),
        )
        for index, change in enumerate(updates):
            with self.subTest(index=index), self.assertRaises(core.InputError):
                research.inspect_packages([edit_result(self.package, change)])

    def test_source_provenance_and_step_reasons_are_data_only(self):
        package = deepcopy(self.package)
        package['source'] = 'axiom injected : False'
        package['original_input'] = 'set_option debug.skipKernelTC true'
        package = repack(package)
        data = gamma_plan(package, 'steps')
        data['proof']['steps'][0]['reason'] = 'axiom reason_injection : False'
        source = research.render(data)
        for text in (package['source'], package['original_input'], data['proof']['steps'][0]['reason']):
            self.assertNotIn(text, source)

    def test_rehashed_derived_dependency_description_is_recomputed_from_source(self):
        derived = boundary_fixture(gamma_plan(self.package), 'Gamma-two')
        research.inspect_packages([derived])
        def change(result):
            result['research_dependencies'][0]['statement'] = 'injected dependency description'
            result['analysis']['dependencies'] = deepcopy(result['research_dependencies'])
        changed = edit_result(derived, change)
        changed['evidence']['analysis.json'] = json.dumps(json.loads(changed['evidence']['result.json'])['analysis'])
        with self.assertRaisesRegex(core.InputError, 'dependency records'):
            research.inspect_packages([repack(changed)])

    def test_derived_bessel_full_flag_is_checked_before_lean(self):
        original = package_from_run(core.ROOT/'demo/integer-y-zero-derivative-direct', 'Y-zero-derivative')
        target = json.loads(original['evidence']['request.json'])
        target['proof'] = {'mode': 'direct', 'recipe': 'research', 'lemmas': [original],
                           'uses': [use(original, {'op': 'var', 'name': 'x'})]}
        derived = boundary_fixture(target, 'Derived-Y-zero')
        research.inspect_packages([derived])
        changed = edit_result(derived, lambda result: result.update(full_bessel_proof=False))
        with patch('special_function_agent.core._run_lean') as runner, \
             self.assertRaisesRegex(core.InputError, 'full Bessel certificate'):
            research.inspect_packages([changed])
        runner.assert_not_called()
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            for name, text in changed['evidence'].items():
                (directory/name).write_text(text)
            with patch('special_function_agent.core._run_lean') as runner, \
                 self.assertRaisesRegex(core.InputError, 'Bessel proof status'):
                core.replay(directory)
            runner.assert_not_called()

    def test_step_chain_and_total_use_bounds_are_checked(self):
        data = gamma_plan(self.package, 'steps')
        data['proof']['steps'][1]['before'] = data['lhs']
        with self.assertRaises(core.InputError): research.render(data)
        data = gamma_plan(self.package)
        data['proof']['uses'] *= 7
        with self.assertRaises(core.InputError): research.render(data)
        data = gamma_plan(self.package)
        data['proof']['lemmas'] *= 2
        with self.assertRaises(core.InputError): research.render(data)

    def test_saved_request_size_and_cached_dependency_height_have_fixed_limits(self):
        data = gamma_plan(self.package)
        saved_bytes = len((json.dumps(data, ensure_ascii=False, indent=2)+'\n').encode())
        with patch.object(research, 'MAX_PLAN_BYTES', saved_bytes-1), self.assertRaises(core.InputError):
            research.render(data)
        with patch.object(research, 'MAX_PLAN_BYTES', saved_bytes): research.render(data)
        # A shared subtree cached from a shallow path must retain its full height.
        context = {'cache': {self.package['id']: {'height': 2}}, 'active': set(),
                   'seen': set(), 'environment': core.environment()}
        with self.assertRaisesRegex(core.InputError, 'depth limit'):
            research._package(self.package, context, research.MAX_DEPTH)


@unittest.skipUnless(os.environ.get('SF_RUN_LEAN_TESTS') == '1' or os.environ.get('BESSEL_RUN_LEAN_TESTS') == '1',
                     'Enable real research-lemma Lean acceptance.')
class ResearchProofLeanTests(unittest.TestCase):
    def verify(self, data, output):
        with patch('special_function_agent.real_numeric.importlib.import_module', side_effect=ImportError):
            return core.verify(data, output, timeout=120)

    def test_gamma_two_both_routes_replay_and_missing_numeric_backend(self):
        package = gamma_package()
        for route in ('direct', 'steps'):
            with self.subTest(route=route), tempfile.TemporaryDirectory() as tmp:
                output = Path(tmp)/'run'
                result = self.verify(gamma_plan(package, route), output)
                self.assertEqual(result['status'], 'proved', result)
                self.assertTrue(result['full_function_proof'])
                self.assertEqual(result['formal_scope'], research.FORMAL_SCOPE)
                self.assertEqual(result['numerical']['diagnostic'], 'backend_unavailable')
                self.assertTrue(set(result['attempts'][-1]['axioms']) <= core.ALLOWED_AXIOMS)
                self.assertTrue(core.replay(output, timeout=120)['replayed'])

    def test_wrong_coefficient_and_source_condition_shortfall_are_lean_rejected(self):
        stronger = parse_identity(GAMMA.replace('x>0', 'x>1'))
        stronger['proof'] = real_special.default_proof(stronger)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.assertEqual(self.verify(stronger, root/'source')['status'], 'proved')
            package = package_from_run(root/'source')
            cases = [case for route in ('direct', 'steps') for case in (
                gamma_plan(gamma_package(), route, text=GAMMA_TWO.replace('=(x+1)', '=2*(x+1)')),
                gamma_plan(package, route))]
            for index, data in enumerate(cases):
                with self.subTest(index=index):
                    result = self.verify(data, root/str(index))
                    self.assertEqual(result['status'], 'unresolved', result)
                    self.assertFalse(result['full_function_proof'])
                    self.assertFalse(result['attempts'][-1]['accepted'])

    def test_reverse_use_and_derived_lemma_reuse_are_compiled_with_transitive_sources(self):
        package = gamma_package()
        reverse = parse_identity('x*Gamma(x)=Gamma(x+1);x>0')
        reverse['proof'] = {'mode': 'direct', 'recipe': 'research', 'lemmas': [package],
                            'uses': [use(package, {'op': 'var', 'name': 'x'}, True)]}
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.assertEqual(self.verify(reverse, root/'reverse')['status'], 'proved')
            self.assertEqual(self.verify(gamma_plan(package), root/'derived')['status'], 'proved')
            derived = package_from_run(root/'derived', 'Gamma-two')
            target = parse_identity('Gamma(x+3)=(x+2)*(x+1)*x*Gamma(x);x>0')
            plus_one = {'op': 'add', 'args': [{'op': 'var', 'name': 'x'}, {'op': 'int', 'value': 1}]}
            target['proof'] = {'mode': 'direct', 'recipe': 'research', 'lemmas': [derived, package],
                               'uses': [use(derived, plus_one), use(package, {'op': 'var', 'name': 'x'})]}
            result = self.verify(target, root/'third')
            self.assertEqual(result['status'], 'proved', result)
            self.assertEqual([item['id'] for item in result['research_dependencies']], [package['id'], derived['id']])
            self.assertTrue(core.replay(root/'third', timeout=120)['replayed'])

    def test_integral_binder_is_capture_free_and_derivative_substitution_keeps_chain_rule(self):
        beta = package_from_run(core.ROOT/'demo/beta-direct', 'Beta')
        target = parse_identity('int(0,1,u^(t-1)*(1-u)^(b-1),u)=Gamma(t)*Gamma(b)/Gamma(t+b);t>0,b>0')
        target['proof'] = {'mode': 'direct', 'recipe': 'research', 'lemmas': [beta], 'uses': [
            {'lemma': beta['id'], 'arguments': {'a': {'op': 'var', 'name': 't'}, 'b': {'op': 'var', 'name': 'b'}},
             'reverse': False}]}
        derivative = package_from_run(core.ROOT/'demo/erf-derivative-direct', 'Erf-derivative')
        false = parse_identity('D_x(erf(2*x))=2/sqrt(pi)*exp(-(2*x)^2);x real')
        false['proof'] = {'mode': 'direct', 'recipe': 'research', 'lemmas': [derivative], 'uses': [
            use(derivative, {'op': 'mul', 'args': [{'op': 'int', 'value': 2}, {'op': 'var', 'name': 'x'}]})]}
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.assertEqual(self.verify(target, root/'beta')['status'], 'proved')
            result = self.verify(false, root/'capture')
            self.assertEqual(result['status'], 'unresolved', result)
            self.assertFalse(result['attempts'][-1]['accepted'])

    def test_forged_accepted_log_cannot_replace_a_real_proof(self):
        data = parse_identity('Gamma(x+1)=3*x*Gamma(x);x>0')
        data['proof'] = {'mode': 'direct', 'recipe': 'ring'}
        forged = boundary_fixture(data)
        with tempfile.TemporaryDirectory() as tmp:
            result = self.verify(gamma_plan(forged), Path(tmp)/'run')
            self.assertEqual(result['status'], 'unresolved', result)
            self.assertFalse(result['attempts'][-1]['accepted'])


if __name__ == '__main__':
    unittest.main()
