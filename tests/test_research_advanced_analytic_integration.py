"""Original equations, analytic contracts, conditions and reusable evidence agree."""
from copy import deepcopy
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

from special_function_agent import core, defined_proof, research_functions as functions
from special_function_agent import research_function_library as library, research_library
from special_function_agent.archive import target_hash
from special_function_agent.real_bessel import labels, _walk
from special_function_agent.research_generation import attach_lemmas

SLUGS = ('geometric', 'elementary', 'nonlinear', 'second-order')
MODULE = 'SpecialFunctionProofAgent/AdvancedAnalyticDefinitions.lean'
I = lambda value: {'op':'int','value':value}
V = lambda name: {'op':'var','name':name}
B = lambda op,a,b: {'op':op,'args':[a,b]}
U = lambda op,arg: {'op':op,'arg':arg}
P = lambda arg,n: {'op':'pow','base':arg,'exponent':n}


def example(slug, kind): return core.load_json(core.ROOT/'examples'/f'research-advanced-{slug}.{kind}.json')
def request(target, route='direct'): return {**deepcopy(target),'proof':defined_proof.default_proof(target,route)}


def target_for(raw):
    snapshot=functions.make_definition(raw)
    call={'op':'defined','function':snapshot['id'],'arguments':{name:V(name) for name in raw['parameters']}}
    return {'schema_version':2,'variables':raw['parameters'],'assumptions':[],'definitions':[snapshot],
            'lhs':call,'rhs':functions.expand_expr(call,[snapshot])}


def derived(slug, package, route):
    target=example(slug,'derived.target')
    uses=[{'lemma':package['id'],'arguments':{name:V(name) for name in target['variables']},'reverse':False}]
    proof=({'mode':'direct','recipe':'research','uses':uses} if route=='direct' else
           {'mode':'steps','steps':[{'before':target['lhs'],'after':target['rhs'],'recipe':'research','uses':uses,
                                    'reason':'定義根拠を検査した補題で両辺を2倍する。','conditions':labels(target)}]})
    return {**target,'proof':attach_lemmas(proof,[package])}


class AdvancedAnalyticBoundaryTests(unittest.TestCase):
    def test_prompt_display_supports_each_new_elementary_function(self):
        for op in ('sin', 'cos', 'sinh', 'arsinh'):
            with self.subTest(op=op):
                self.assertIn(op, core.display_expr(U(op, V('x'))))
        from special_function_agent.generate import make_prompt, output_schema
        for slug in SLUGS:
            prompt=make_prompt(example(slug,'source.target'),'steps')
            self.assertIn('Copy the original lhs/rhs AST exactly',prompt)
            schema=output_schema('steps',example(slug,'source.target'))
            unary=[node['properties']['op'].get('enum',[]) for node in schema['$defs']['expr']['anyOf']
                   if 'arg' in node['properties']]
            self.assertTrue(any(set(('sin','cos','sinh','arsinh')) <= set(ops) for ops in unary))

    def test_original_formula_types_initial_data_and_identity_are_preserved(self):
        for slug in SLUGS:
            raw,target=example(slug,'definition'),example(slug,'source.target')
            with self.subTest(slug=slug):
                self.assertEqual(target_for(raw),target)
                contract=functions.metadata(target['definitions'])[0]['analytic_contracts'][0]
                self.assertEqual(contract['semantics']['original'],raw['body'])
                self.assertEqual(contract['semantics']['normalized']['original'],raw['body'])
                self.assertNotEqual(target_hash(target),target_hash(example(slug,'derived.target')))
                for route in ('direct','steps'):
                    checked=request(target,route);core.validate_request(checked)
                    self.assertEqual(target_hash(checked),target_hash(target))
                    self.assertEqual({k:v for k,v in checked.items() if k!='proof'},target)

    def test_contracts_contain_convergence_integrability_and_each_solution_class(self):
        for slug,statement,theorem in (
            ('geometric','HasSum','hasSum_geometricCombination'),
            ('elementary','IntervalIntegrable','intervalIntegrable_elementaryCombination'),
            ('nonlinear','∃! y : ℝ → ℝ','existsUnique_nonlinearPolynomialIVPSolution'),
            ('second-order','∃! state : (ℝ → ℝ) × (ℝ → ℝ)','existsUnique_polynomialSecondOrderSolution')):
            with self.subTest(slug=slug):
                source=functions.render_definition(example(slug,'source.target')['definitions'][0])
                self.assertIn(statement,source.split('theorem target',1)[1]);self.assertIn(theorem,source)
                self.assertNotIn('sorry',source);self.assertNotIn('axiom ',source)
                self.assertIn('AdvancedAnalyticDefinitions',source)
        source=functions.render_definition(example('second-order','source.target')['definitions'][0])
        self.assertIn('HasDerivAt state.1 (state.2',source)
        self.assertIn('HasDerivAt state.2',source)
        self.assertIn('state.1 (',source);self.assertIn('state.2 (',source)

    def test_new_module_is_scoped_and_previous_public_environments_are_unchanged(self):
        self.assertNotIn(MODULE,core.environment());count=0
        for out in (core.ROOT/'demo').iterdir():
            if not (out/'result.json').exists():continue
            data=core.load_json(out/'request.json')
            if functions.uses_advanced_analytic(data):continue
            self.assertEqual(functions.environment(data),core.load_json(out/'result.json')['environment'],out.name)
            count+=1
        self.assertGreaterEqual(count,141)
        for slug in SLUGS:self.assertIn(MODULE,functions.environment(example(slug,'source.target')))

    def test_module_revision_changes_environment_but_preserves_semantics(self):
        read=Path.read_bytes
        def changed(path):
            content=read(path)
            return content+b'\n-- changed environment\n' if path==core.ROOT/MODULE else content
        for slug in SLUGS:
            target=example(slug,'source.target');before=functions.environment(target)
            identity=target_hash(target);conventions=defined_proof.conventions(target)
            with self.subTest(slug=slug),patch.object(Path,'read_bytes',changed):
                self.assertNotEqual(functions.environment(target)[MODULE],before[MODULE])
                self.assertEqual(target_hash(target),identity)
                self.assertEqual(defined_proof.conventions(target),conventions)

    def test_returned_conventions_and_metadata_cannot_mutate_later_evidence(self):
        target=example('nonlinear','source.target')
        conventions=defined_proof.conventions(target)
        definition=functions.definition_conventions(target['definitions'][0])
        metadata=functions.metadata(target['definitions'])
        expected=deepcopy(conventions)
        conventions['advanced_real_functions']['arsinh']='changed'
        definition['advanced_real_functions']['arsinh']='changed'
        metadata[0]['analytic_contracts'][0]['semantics']['elementary_functions']['arsinh']='changed'
        self.assertEqual(defined_proof.conventions(target),expected)
        self.assertEqual(functions.definition_conventions(target['definitions'][0])['advanced_real_functions']['arsinh'],
                         expected['advanced_real_functions']['arsinh'])

    def test_candidate_cannot_replace_target_assumptions_definitions_or_submit_lean(self):
        for slug in SLUGS:
            target=example(slug,'source.target');proof=defined_proof.default_proof(target,'steps')
            for field,value in [('target',{'rhs':I(0)}),('assumptions',[]),('definitions',[]),('lean','axiom injected : False')]:
                with self.subTest(slug=slug,field=field),self.assertRaises(core.InputError):
                    core.validate_request({**target,'proof':{**proof,field:value}})
            self.assertEqual(proof['steps'][0]['conditions'],labels(target))

    def test_cancelled_finite_coefficient_domain_is_retained_without_added_assumptions(self):
        raw=example('elementary','definition');term=B('div',U('exp',V('t')),V('a'))
        raw['body']['integrand']=B('sub',term,term)
        target=target_for(raw);target['rhs']=I(0)
        with tempfile.TemporaryDirectory() as directory,patch('special_function_agent.real_special._run_lean') as lean:
            output=Path(directory)/'proof';result=core.verify(request(target),output,timeout=90)
            self.assertEqual(result['status'],'needs_conditions');lean.assert_not_called()
            self.assertEqual(core.load_json(output/'request.json')['assumptions'],[])
        self.assertIn(V('a'),functions.metadata(target['definitions'])[0]['analytic_contracts'][0]['semantics']['normalized']['nonzero_denominators'])


@unittest.skipUnless(os.environ.get('SF_RUN_LEAN_TESTS')=='1','Set SF_RUN_LEAN_TESTS=1 for advanced analytic Lean integration.')
class AdvancedAnalyticLeanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary=tempfile.TemporaryDirectory(prefix='sf-advanced-integration-');cls.root=Path(cls.temporary.name)
        cls.packages={};cls.functions={}
        for slug in SLUGS:
            cls.functions[slug]=library.register(example(slug,'definition'),cls.root/'research',timeout=120)
            result=core.verify(request(example(slug,'source.target')),cls.root/slug,timeout=120)
            if result['status']!='proved':raise AssertionError((slug,result))
            cls.packages[slug]=research_library.register(cls.root/slug,cls.root/'research',name='advanced-'+slug,timeout=120)

    @classmethod
    def tearDownClass(cls):cls.temporary.cleanup()
    def location(self):return Path(tempfile.mkdtemp(dir=self.root))/'proof'

    def test_registration_source_steps_and_replay_all_four_classes(self):
        for slug in SLUGS:
            with self.subTest(slug=slug):
                self.assertEqual(self.functions[slug]['verification']['status'],'defined')
                self.assertTrue(set(self.functions[slug]['verification']['axioms']) <= core.ALLOWED_AXIOMS)
                out=self.location();result=core.verify(request(example(slug,'source.target'),'steps'),out,timeout=120)
                self.assertEqual(result['status'],'proved',result);self.assertTrue(core.replay(out,timeout=120)['replayed'])
                source=(out/'certificate.lean').read_text()
                self.assertIn('theorem expanded_target',source);self.assertIn('ResearchAdvanced_',source)
                self.assertIn('theorem target',source)

    def test_registered_lemmas_prove_different_targets_both_routes(self):
        for slug in SLUGS:
            for route in ('direct','steps'):
                with self.subTest(slug=slug,route=route):
                    out=self.location();result=core.verify(derived(slug,self.packages[slug],route),out,timeout=120)
                    self.assertEqual(result['status'],'proved',result)
                    self.assertIn('ResearchLemma_'+self.packages[slug]['id']+'.expanded_target',(out/'certificate.lean').read_text())
                    if route=='steps':self.assertTrue(core.replay(out,timeout=120)['replayed'])

    def test_variants_negative_initial_values_reverse_endpoints_and_independent_velocity(self):
        raws={slug:example(slug,'definition') for slug in SLUGS}
        q=B('div',V('x'),B('add',P(V('x'),2),I(1)))
        raws['geometric']['body']['term']=P(U('neg',q),V('k'))
        raws['elementary']['body'].update(lower=I(3),upper=I(-2),integrand=U('cos',V('x')))
        raws['nonlinear']['body'].update(initial_time=V('a'),initial_value=I(-3))
        raws['second-order']['body'].update(initial_time=I(-2),initial_value=V('v0'),initial_derivative=V('c'))
        for slug,raw in raws.items():
            with self.subTest(slug=slug):
                result=core.verify(request(target_for(raw)),self.location(),timeout=120)
                self.assertEqual(result['status'],'proved',result)

    def test_changed_formula_endpoint_and_independent_initial_conditions_are_rejected(self):
        cases=[]
        wrong=example('geometric','source.target');wrong['rhs']=B('add',wrong['rhs'],I(1));cases.append(wrong)
        wrong=example('elementary','source.target');wrong['lhs']['arguments'].update(a=V('b'),b=V('a'));cases.append(wrong)
        for slug,field in [('nonlinear','initial_value'),('second-order','initial_value'),('second-order','initial_derivative')]:
            raw=example(slug,'definition');raw['body'][field]=B('add',raw['body'][field],I(1))
            wrong=target_for(raw);wrong['rhs']=example(slug,'source.target')['rhs'];cases.append(wrong)
        for index,target in enumerate(cases):
            for route in ('direct','steps'):
                with self.subTest(case=index,route=route):
                    out=self.location();result=core.verify(request(target,route),out,timeout=120)
                    self.assertNotEqual(result['status'],'proved',result);self.assertFalse((out/'certificate.lean').exists())

    def test_explicit_original_nonzero_condition_discharge_and_replay(self):
        raw=example('elementary','definition');term=B('div',U('exp',V('t')),V('a'));raw['body']['integrand']=B('sub',term,term)
        target=target_for(raw);target['rhs']=I(0)
        target['assumptions']=[{'op':'compare','variable':'a','relation':'ne','value':{'numerator':0,'denominator':1}}]
        out=self.location();result=core.verify(request(target),out,timeout=120)
        self.assertEqual(result['status'],'proved',result);self.assertTrue(core.replay(out,timeout=120)['replayed'])
        self.assertEqual(core.load_json(out/'request.json')['assumptions'],target['assumptions'])

    def test_internal_and_outer_calculus_bindings_do_not_capture_parameters(self):
        snapshot=example('elementary','source.target')['definitions'][0]
        call={'op':'defined','function':snapshot['id'],'arguments':{'a':I(0),'b':I(1),'x':V('at0')}}
        for kind in ('deriv','integral'):
            lhs={'op':'deriv','var':'at0','arg':call} if kind=='deriv' else {'op':'integral','var':'at0','lower':I(-1),'upper':I(2),'body':call}
            target={'schema_version':2,'variables':{'at0':'real'} if kind=='deriv' else {'u':'real'},'assumptions':[],
                    'definitions':[snapshot],'lhs':lhs,'rhs':functions.expand_expr(lhs,[snapshot])}
            with self.subTest(kind=kind):
                result=core.verify(request(target),self.location(),timeout=120);self.assertEqual(result['status'],'proved',result)

    def test_saved_contract_and_source_tampering_are_rejected(self):
        for kind in ('source','contract'):
            out=self.location();shutil.copytree(self.root/'second-order',out)
            if kind=='source':(out/'certificate.lean').write_text((out/'certificate.lean').read_text()+'\naxiom injected : False\n')
            else:
                data=core.load_json(out/'analysis.json')
                data['definitions'][0]['analytic_contracts'][0]['semantics']['original']['initial_derivative']=I(999)
                (out/'analysis.json').write_text(json.dumps(data))
            with self.subTest(kind=kind),self.assertRaises(core.InputError):core.replay(out,timeout=120)

    def test_environment_reverification_appends_record_and_keeps_original_bytes(self):
        package=self.functions['nonlinear'];path=self.root/'research/functions'/(package['id']+'.json');old=path.read_bytes();read=Path.read_bytes
        def changed(p):
            data=read(p);return data+b'\n-- revision\n' if p==core.ROOT/MODULE else data
        with patch.object(Path,'read_bytes',changed):
            with self.assertRaisesRegex(core.InputError,'environment'):library.definitions([package])
            updated=library.reverify(package['id'],self.root/'research',timeout=120)['package']
            self.assertNotEqual(updated['id'],package['id']);self.assertEqual(updated['definition'],package['definition'])
        self.assertEqual(path.read_bytes(),old)


if __name__=='__main__':unittest.main()
