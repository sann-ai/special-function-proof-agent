"""Finite definitions retain types, simultaneous substitution, and lexical binding."""
from copy import deepcopy
import json
import os
from pathlib import Path
import tempfile
import unittest

from special_function_agent import core, real_bessel, real_special
from special_function_agent import research_functions as functions


def var(name): return {'op': 'var', 'name': name}
def integer(value): return {'op': 'int', 'value': value}
def binary(op, left, right): return {'op': op, 'args': [left, right]}
def call(definition, **arguments): return {'op': 'defined', 'function': definition['id'], 'arguments': arguments}


def raw(name='ShiftedGamma', body=None, parameters=None, definitions=None):
    return {'schema_version': 1, 'name': name, 'parameters': parameters or {'u': 'real'},
            'body': body if body is not None else {'op': 'gamma', 'arg': binary('add', var('u'), integer(1))},
            'definitions': definitions or []}


def definition(**kwargs): return functions.make_definition(raw(**kwargs))


def target(definitions, lhs, rhs, variables=None, assumptions=None, proof=None):
    return {'schema_version': 2, 'variables': variables if variables is not None else {'x': 'real'},
            'assumptions': assumptions or [], 'lhs': lhs, 'rhs': rhs, 'definitions': definitions,
            'proof': proof or {'mode': 'direct', 'recipe': 'ring'}}


def positive(name='x'):
    return {'op': 'compare', 'variable': name, 'relation': 'gt', 'value': {'numerator': 0, 'denominator': 1}}


class ResearchFunctionBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.shift = definition()

    def test_semantic_id_is_canonical_and_parameters_have_sorted_lean_order(self):
        first = raw(name='Difference', body=binary('sub', var('u'), var('v')),
                    parameters={'v': 'real', 'u': 'real'})
        second = {key: first[key] for key in reversed(first)}
        second['parameters'] = {'u': 'real', 'v': 'real'}
        left, right = functions.make_definition(first), functions.make_definition(second)
        self.assertEqual(left['id'], right['id'])
        self.assertEqual(functions.lean_definitions([left]), functions.lean_definitions([right]))
        self.assertIn('(p0 : ℝ) (p1 : ℝ)', functions.lean_definitions([left]))
        self.assertIn('(p0 - p1)', functions.lean_definitions([left]))
        self.assertEqual(functions.metadata([left])[0]['lean_name'], 'ResearchFunction_'+left['id'])

    def test_function_names_types_and_parameter_collisions_are_rejected(self):
        for name in ('Gamma', 'gamma', 'GAMMA', 'X', 'x', 'theorem', 'a-b', 'λ', 'ResearchFunction_custom'):
            with self.subTest(name=name), self.assertRaises(core.InputError): definition(name=name)
        for parameters in ({'u': 'nat'}, {'u': 'int'}, {'u': 'complex'}, {'u': 'real', 'U': 'real'},
                           {'ShiftedGamma': 'real'}, {'u': 'real', 'v': 'real', 'w': 'real', 'z': 'real'}):
            with self.subTest(parameters=parameters), self.assertRaises(core.InputError): definition(parameters=parameters)
        valid = definition(name='Coordinate', parameters={'x': 'real'}, body=var('x'))
        self.assertEqual(functions.expand_expr(call(valid, x=var('x')), [valid]), var('x'))

    def test_closed_fields_and_changed_meaning_are_detected(self):
        for extra in ('source', 'environment', 'lean', 'assumptions'):
            data = raw(); data[extra] = 'untrusted'
            with self.subTest(extra=extra), self.assertRaises(core.InputError): functions.make_definition(data)
        changed = deepcopy(self.shift); changed['body']['arg']['args'][1]['value'] = 2
        with self.assertRaisesRegex(core.InputError, 'ID differs'): functions.validate_definition(changed)
        changed = deepcopy(self.shift); changed['id'] = '0'*64
        with self.assertRaises(core.InputError): functions.validate_definition(changed)

    def test_bodies_reject_calculus_unknown_variables_and_free_degrees(self):
        cases = [var('missing'), {'op': 'deriv', 'var': 'u', 'arg': var('u')}, {'op': 'infinity'},
                 {'op': 'integral', 'var': 't', 'lower': integer(0), 'upper': integer(1), 'body': var('t')},
                 {'op': 'legendre', 'order': var('n'), 'arg': var('u')},
                 {'op': 'bessel_j', 'order': var('n'), 'arg': var('u')}]
        for body in cases:
            with self.subTest(body=body), self.assertRaises(core.InputError): definition(body=body)

    def test_dependency_closure_rejects_unused_unknown_duplicate_and_colliding_definitions(self):
        valid = definition(name='ShiftTwice', body=call(self.shift, u=binary('add', var('u'), integer(1))),
                           definitions=[self.shift])
        self.assertEqual([item['id'] for item in functions.metadata([valid])], [self.shift['id'], valid['id']])
        for data in (raw(name='Unused', body=var('u'), definitions=[self.shift]),
                     raw(name='Unknown', body=call(self.shift, u=var('u'))),
                     raw(name='Repeated', body=call(self.shift, u=var('u')), definitions=[self.shift, self.shift])):
            with self.subTest(name=data['name']), self.assertRaises(core.InputError): functions.make_definition(data)
        other = definition(body=var('u'))
        with self.assertRaises(core.InputError): functions.metadata([self.shift, other])
        with self.assertRaises(core.InputError): functions.metadata([self.shift, self.shift])

    def test_depth_cycle_and_bytes_are_bounded(self):
        nested = self.shift
        for depth in range(2, 5):
            nested = definition(name='Nested'+str(depth), body=call(nested, u=var('u')), definitions=[nested])
        with self.assertRaisesRegex(core.InputError, 'depth four'):
            definition(name='TooDeep', body=call(nested, u=var('u')), definitions=[nested])
        cyclic = raw(name='Cyclic'); cyclic['definitions'].append(cyclic)
        with self.assertRaises(core.InputError): functions.make_definition(cyclic)
        too_large = raw(name='Huge', body={'op': 'var', 'name': 'u'*(functions.MAX_BYTES+1)})
        with self.assertRaises(core.InputError): functions.make_definition(too_large)

    def test_substitution_is_simultaneous_and_nested_calls_are_expanded(self):
        difference = definition(name='Difference', body=binary('sub', var('u'), var('v')),
                                parameters={'u': 'real', 'v': 'real'})
        swapped = call(difference, u=var('v'), v=var('u'))
        self.assertEqual(functions.expand_expr(swapped, [difference]), binary('sub', var('v'), var('u')))
        nested = call(self.shift, u=call(difference, u=var('v'), v=var('u')))
        expanded = functions.expand_expr(nested, [self.shift, difference])
        self.assertEqual(expanded['arg']['args'][0], binary('sub', var('v'), var('u')))
        self.assertFalse(functions.contains(expanded))

    def test_constant_function_still_checks_every_discarded_argument(self):
        constant = definition(name='ConstantOne', body=integer(1))
        self.assertEqual(functions.expand_expr(call(constant, u=var('x')), [constant]), integer(1))
        for argument, variables in [(var('undeclared'), {'x': 'real'}), (var('n'), {'n': 'nat'}),
                                    (var('n'), {'n': 'int'}),
                                    ({'op': 'deriv', 'var': 'x', 'arg': var('x')}, {'x': 'real'})]:
            data = target([constant], call(constant, u=argument), integer(1), variables)
            with self.subTest(argument=argument), self.assertRaises(core.InputError): functions.validate_target(data)
        with self.assertRaises(core.InputError):
            definition(name='HiddenVariable', body=call(constant, u=var('undeclared')), definitions=[constant])

    def test_argument_keys_real_degree_and_rational_positions_are_checked(self):
        for arguments in ({}, {'u': var('x'), 'v': var('x')}):
            with self.assertRaises(core.InputError): functions.expand_expr(call(self.shift, **arguments), [self.shift])
        degree = {'op': 'legendre', 'order': call(self.shift, u=integer(1)), 'arg': var('x')}
        with self.assertRaises(core.InputError): functions.expand_expr(degree, [self.shift])
        rational = {'op': 'rational', 'numerator': 1, 'denominator': 2}
        half = definition(name='HalfScale', body=binary('mul', rational, var('u')))
        self.assertEqual(functions.expand_expr(call(half, u=var('x')), [half]),
                         binary('mul', binary('div', integer(1), integer(2)), var('x')))
        bessel = definition(name='HalfOrder', body={'op': 'bessel_j', 'order': rational, 'arg': var('u')})
        self.assertEqual(functions.expand_expr(call(bessel, u=var('x')), [bessel])['order'], rational)

    def test_outer_integral_and_derivative_keep_lexical_bindings_and_parameter_dependence(self):
        product = definition(name='Product', body=binary('mul', var('u'), var('v')), parameters={'u': 'real', 'v': 'real'})
        inner = call(product, u=var('t'), v=var('x'))
        integral = {'op': 'integral', 'var': 't', 'lower': integer(0), 'upper': integer(1), 'body': inner}
        data = target([product], integral, integer(0))
        functions.validate_target(data)
        expanded = functions.expand_target(data)
        self.assertEqual(expanded['lhs']['body'], binary('mul', var('t'), var('x')))
        dependent = {'op': 'deriv', 'var': 'x', 'arg': call(product, u=var('x'), v=var('x'))}
        expanded = functions.expand_target(target([product], dependent, integer(0)))
        self.assertEqual(expanded['lhs']['arg'], binary('mul', var('x'), var('x')))
        data['lhs']['var'] = 'x'
        with self.assertRaises(core.InputError): functions.validate_target(data)

    def test_original_step_chain_is_checked_before_equal_expansions_and_evidence_stays_fixed(self):
        twin = definition(name='OtherShift')
        left, right = call(self.shift, u=var('x')), call(twin, u=var('x'))
        proof = {'mode': 'steps', 'steps': [{'before': right, 'after': right, 'recipe': 'ring',
                                            'reason': 'rfl', 'conditions': []}]}
        with self.assertRaises(core.InputError): functions.expand_target(target([self.shift, twin], left, right, proof=proof))
        evidence = {'evidence': {'request.json': json.dumps({'definitions': [self.shift], 'lhs': left})}}
        proof = {'mode': 'direct', 'recipe': 'research', 'lemmas': [evidence],
                 'uses': [{'lemma': '0'*64, 'arguments': {'x': left}, 'reverse': False}]}
        data = target([self.shift], left, right, proof=proof)
        data['rhs'] = left
        expanded = functions.expand_target(data)
        self.assertEqual(expanded['proof']['lemmas'], [evidence])
        self.assertFalse(functions.contains({'proof': {'lemmas': [{'definitions': [self.shift]}]}}))
        self.assertEqual(expanded['proof']['uses'][0]['arguments']['x'], expanded['lhs'])

    def test_definition_typing_defers_gamma_and_denominator_domains_to_use(self):
        normalized = definition(name='NormalizedGamma', body=binary('div', {'op': 'gamma', 'arg': var('u')}, var('u')))
        data = target([normalized], call(normalized, u=var('x')), integer(0))
        expanded = functions.expand_target(data)
        self.assertIn('x != 0', real_bessel.domain_obligations(expanded, None))
        self.assertFalse(real_bessel._positive(expanded['lhs']['args'][0]['arg'], real_bessel.domains(expanded)))
        total = definition(name='ZeroDenominator', body=binary('div', integer(1), integer(0)))
        with self.assertRaises(core.NeedsConditions):
            functions.validate_target(target([total], call(total, u=var('x')), integer(0)))

    def test_defined_condition_labels_are_mapped_from_the_original_fixed_conditions(self):
        coordinate = definition(name='Coordinate', body=var('u'))
        expr = call(coordinate, u=var('x'))
        condition = {'op': 'expr_compare', 'lhs': expr, 'relation': 'ne', 'rhs': integer(0)}
        data = target([coordinate], expr, var('x'), assumptions=[condition])
        label = real_bessel.labels(data)[-1]
        data['proof'] = {'mode': 'steps', 'steps': [{'before': expr, 'after': var('x'), 'recipe': 'ring',
                                                   'reason': '定義を展開する。', 'conditions': [label]}]}
        functions.validate_target(data)
        expanded = functions.expand_target(data)
        self.assertEqual(expanded['proof']['steps'][0]['conditions'], ['x != 0'])
        self.assertEqual(data['proof']['steps'][0]['conditions'], [label])
        invalid = deepcopy(data)
        invalid['assumptions'][0]['rhs'] = call(coordinate, u=integer(0))
        with self.assertRaises(core.InputError): functions.expand_target(invalid)

    def test_conventions_include_transitive_families_and_top_level_selection_is_preserved(self):
        erf = definition(name='ErrorFunction', body={'op': 'erf', 'arg': var('u')})
        outer = definition(name='ComposedError', body=call(erf, u=var('u')), definitions=[erf])
        self.assertEqual(functions.definition_conventions(outer)['version'], 2)
        data = target([self.shift, outer], call(self.shift, u=var('x')), integer(0))
        original = deepcopy(data)
        functions.expand_target(data)
        self.assertEqual(data, original)
        self.assertEqual(len(functions.metadata(data['definitions'])), 3)


@unittest.skipUnless(os.environ.get('SF_RUN_LEAN_TESTS') == '1' or os.environ.get('BESSEL_RUN_LEAN_TESTS') == '1',
                     'Enable real finite-definition Lean acceptance.')
class ResearchFunctionLeanTests(unittest.TestCase):
    def check(self, source):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'definition.lean'; path.write_text(source)
            outcome = core._run_lean(path, 120)
            self.assertTrue(outcome['accepted'], outcome)
            self.assertTrue(set(outcome['axioms']) <= core.ALLOWED_AXIOMS)

    def test_definitions_and_nested_real_compositions_compile_with_standard_axioms(self):
        shift = definition()
        normalized = definition(name='NormalizedGamma', body=binary('div', call(shift, u=var('u')), var('u')),
                                definitions=[shift])
        power = definition(name='PoweredGamma', body={'op': 'gamma', 'arg': {
            'op': 'rpow', 'base': var('u'), 'exponent': binary('div', integer(1), integer(2))}})
        rational = definition(name='HalfScale', body=binary('mul', var('u'),
                              {'op': 'rational', 'numerator': 1, 'denominator': 2}))
        for item in (shift, normalized, power, rational, definition(name='ConstantOne', body=integer(1))):
            with self.subTest(name=item['name']): self.check(functions.render_definition(item))

    def test_call_renderer_and_expansion_agree_under_nested_calculus_binders(self):
        product = definition(name='Product', body=binary('mul', var('u'), var('v')), parameters={'u': 'real', 'v': 'real'})
        derivative = {'op': 'deriv', 'var': 'x', 'arg': {'op': 'deriv', 'var': 'y',
                      'arg': call(product, u=var('x'), v=var('y'))}}
        integral = {'op': 'integral', 'var': 't', 'lower': integer(0), 'upper': integer(1),
                    'body': call(product, u=var('t'), v=var('x'))}
        for expression in (derivative, integral):
            with self.subTest(op=expression['op']):
                data = target([product], expression, expression, {'x': 'real', 'y': 'real'})
                functions.validate_target(data)
                names, types = {'x': 'v0', 'y': 'v1'}, data['variables']
                lhs = functions.lean_expr(expression, names, types, [product])
                rhs = real_special.lean_expr(functions.expand_expr(expression, [product]), names, types)
                source = ('import SpecialFunctionProofAgent\nopen scoped Real\nopen MeasureTheory\n'
                          +functions.lean_definitions([product])+'\nnamespace BesselAgentCandidate\n'
                          +f'theorem target (v0 v1 : ℝ) : {lhs} = {rhs} := by rfl\nend BesselAgentCandidate\n'
                          +'#eval IO.println "BESSEL_AUDIT_BEGIN"\n#print axioms BesselAgentCandidate.target\n'
                          +'#eval IO.println "BESSEL_AUDIT_END"\n')
                self.check(source)


if __name__ == '__main__':
    unittest.main()
