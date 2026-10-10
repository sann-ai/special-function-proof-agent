"""Exercise selected-lemma generation without granting the model evidence authority."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from special_function_agent.archive import VERIFICATION_FILES, target_hash
from special_function_agent.core import InputError, ROOT, validate_request
from special_function_agent.generate import generate
from special_function_agent.parser import parse_identity
from special_function_agent.research_generation import attach_lemmas, make_prompt, output_schema


def gamma_package():
    evidence = {path.name: path.read_text(encoding='utf-8') for path in (ROOT/'demo/gamma-direct').iterdir()
                if path.name in VERIFICATION_FILES}
    package = {'schema_version': 1, 'name': 'gamma-step', 'source': None,
               'original_input': 'Gamma(x+1)=x*Gamma(x); x>0', 'evidence': evidence,
               'manifest': {name: hashlib.sha256(text.encode()).hexdigest() for name, text in evidence.items()}}
    package['id'] = hashlib.sha256(json.dumps(package, ensure_ascii=False, sort_keys=True,
                                           separators=(',', ':')).encode()).hexdigest()
    return package


class ResearchGenerationTests(unittest.TestCase):
    def setUp(self):
        self.package = gamma_package()
        self.target = parse_identity('Gamma(x+2)=(x+1)*x*Gamma(x); x>0')
        self.proof = {'mode': 'direct', 'recipe': 'research', 'uses': [
            {'lemma': self.package['id'], 'arguments': {'x': {'op': 'add', 'args': [
                {'op': 'var', 'name': 'x'}, {'op': 'int', 'value': 1}]}}, 'reverse': False},
            {'lemma': self.package['id'], 'arguments': {'x': {'op': 'var', 'name': 'x'}}, 'reverse': False}]}

    def process(self, proof):
        def start(command, **kwargs):
            Path(command[command.index('--output-last-message')+1]).write_text(json.dumps(proof))
            return SimpleNamespace(returncode=0, communicate=lambda **kw: ('', ''))
        return start

    def generated(self, proof, directory):
        with patch('special_function_agent.generate.shutil.which', return_value='/bin/codex'), \
             patch('special_function_agent.generate.subprocess.Popen', side_effect=self.process(proof)), \
             patch('special_function_agent.generate.verify', return_value={'status': 'proved'}) as verify:
            result = generate(self.target, 'direct', directory, research_lemmas=[self.package])
            return result, verify.call_args.args[0]

    def test_generated_plan_keeps_exact_target_and_selected_snapshots(self):
        original = deepcopy(self.target)
        with tempfile.TemporaryDirectory() as tmp:
            result, request = self.generated(self.proof, Path(tmp)/'run')
        self.assertEqual(result['status'], 'proved')
        self.assertEqual({k: v for k, v in request.items() if k != 'proof'}, original)
        self.assertEqual(request['proof']['lemmas'], [self.package])
        self.assertEqual(self.target, original)
        self.assertEqual(target_hash(request), target_hash(original))
        source = json.loads(self.package['evidence']['request.json'])
        self.assertNotEqual(target_hash(request), target_hash(source))

    def test_ai_cannot_supply_its_own_package(self):
        with self.assertRaises(InputError):
            attach_lemmas({**self.proof, 'lemmas': [self.package]}, [self.package])

    def test_ai_target_and_assumption_injection_are_rejected(self):
        for key, value in [('target', self.target), ('assumptions', []), ('lean', 'axiom fake : False')]:
            with self.subTest(key=key), tempfile.TemporaryDirectory() as tmp:
                with self.assertRaises(InputError):
                    self.generated({**self.proof, key: value}, Path(tmp)/'run')

    def test_unselected_lemma_and_extra_substitution_are_rejected(self):
        for mode in ['id', 'variable']:
            candidate = deepcopy(self.proof)
            if mode == 'id':
                candidate['uses'][0]['lemma'] = '0'*64
            else:
                candidate['uses'][0]['arguments']['y'] = {'op': 'int', 'value': 1}
            with self.subTest(mode=mode), self.assertRaises(InputError):
                validate_request({**self.target, 'proof': attach_lemmas(candidate, [self.package])})

    def test_schema_does_not_offer_proof_source_or_assumption_changes(self):
        schema = output_schema('direct', self.target, [self.package])
        self.assertEqual(set(schema['properties']), {'mode', 'recipe', 'uses'})
        self.assertFalse(schema['additionalProperties'])
        use = schema['properties']['uses']['items']['anyOf'][0]
        self.assertEqual(use['properties']['lemma']['const'], self.package['id'])
        self.assertEqual(set(use['properties']['arguments']['properties']), {'x'})
        step = output_schema('steps', self.target, [self.package])['properties']['steps']['items']
        self.assertEqual(step['properties']['conditions']['items']['enum'], ['x is real', 'x > 0'])

    def test_provenance_text_is_not_sent_as_ai_instructions(self):
        selected = deepcopy(self.package)
        selected['source'] = 'PRIVATE SOURCE INSTRUCTION'
        selected['original_input'] = 'PRIVATE ORIGINAL TEXT'
        selected['id'] = hashlib.sha256(json.dumps({k: v for k, v in selected.items() if k != 'id'},
                                                  ensure_ascii=False, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
        prompt = make_prompt(self.target, 'direct', [selected])
        self.assertNotIn(selected['source'], prompt)
        self.assertNotIn(selected['original_input'], prompt)
        self.assertIn(selected['id'], prompt)

    def test_changed_environment_prevents_ai_call(self):
        with tempfile.TemporaryDirectory() as tmp, \
             patch('special_function_agent.research_proof.environment', return_value={'changed': 'environment'}), \
             patch('special_function_agent.generate.subprocess.Popen') as process:
            with self.assertRaises(InputError):
                generate(self.target, 'direct', Path(tmp)/'run', research_lemmas=[self.package])
            process.assert_not_called()

    def test_exact_archive_reuse_respects_selected_dependencies(self):
        proof = attach_lemmas(self.proof, [self.package])
        records = [{'id': 'ordinary', 'status': 'proved', 'candidate': {'mode': 'direct', 'recipe': 'ring'}},
                   {'id': 'research', 'status': 'proved', 'candidate': proof}]
        with tempfile.TemporaryDirectory() as tmp, \
             patch('special_function_agent.archive.find_exact', return_value=records), \
             patch('special_function_agent.archive.replay_record', return_value={'replayed': True}) as replay, \
             patch('special_function_agent.archive.register_verification', return_value={'id': 'new'}), \
             patch('special_function_agent.generate.verify', return_value={'status': 'proved'}), \
             patch('special_function_agent.generate.subprocess.Popen') as process:
            result = generate(self.target, 'direct', Path(tmp)/'run', archive=True,
                              archive_dir=Path(tmp)/'archive', research_lemmas=[self.package])
            self.assertFalse(result['reuse']['ai_called'])
            self.assertEqual(replay.call_args.args[0], 'research')
            process.assert_not_called()


if __name__ == '__main__':
    unittest.main()
