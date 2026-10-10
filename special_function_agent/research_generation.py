"""Closed AI plans selecting existing, explicitly chosen research packages."""
from copy import deepcopy
import json

from .core import InputError
from .generate import obj, output_schema as ordinary_schema
from .research_library import read_evidence_json


def attach_lemmas(proof, packages):
    if not isinstance(proof, dict) or 'lemmas' in proof:
        raise InputError('The verifier supplies the selected lemma snapshots; a plan cannot replace them.')
    return {**deepcopy(proof), 'lemmas': deepcopy(packages)}


def output_schema(route, target, packages):
    from .research_proof import inspect_packages
    inspect_packages(packages)
    base = ordinary_schema('steps', target, real_ast=True)
    ref = {'$ref': '#/$defs/expr'}
    uses = []
    for package in packages:
        request = read_evidence_json(package, 'request.json')
        uses.append(obj({'lemma': {'const': package['id']},
                         'arguments': obj({name: ref for name in request['variables']}),
                         'reverse': {'type': 'boolean'}}))
    use_array = {'type': 'array', 'items': {'anyOf': uses}, 'minItems': 1, 'maxItems': 12}
    if route == 'direct':
        result = obj({'mode': {'const': 'direct'}, 'recipe': {'const': 'research'}, 'uses': use_array})
    elif route == 'steps':
        step = base['properties']['steps']['items']
        step['properties']['recipe'] = {'type': 'string', 'enum': ['research', 'ring']}
        step['properties']['uses'] = {**use_array, 'minItems': 0}
        step['required'].append('uses')
        result = base
    else:
        raise InputError('Choose a direct or steps research proof.')
    result['$defs'] = base['$defs']
    return result


def make_prompt(target, route, packages, previous_error=''):
    lemmas = []
    for package in packages:
        request = read_evidence_json(package, 'request.json')
        lemmas.append({'id': package['id'], 'target': {key: value for key, value in request.items() if key != 'proof'}})
    prompt = """Return one JSON proof plan matching the schema. Do not use tools or edit files.
The exact typed target and its assumptions are fixed. Use the supplied verified real lemmas.
Each use contains lemma (its exact ID), arguments (all lemma variables mapped to typed real
expressions over the target's free variables), and reverse (swap the lemma equality).
The verifier regenerates each lemma's proof, derives every substituted premise from the
original target assumptions, then rewrites in the listed order and normalizes real algebra.
All free variables are real. Substitution expressions cannot contain derivatives or integrals.
Keep source integral and derivative bindings intact. Do not add or strengthen assumptions.
Direct: recipe research and a nonempty uses list. Steps: exact consecutive before/after
equalities, recipe research with uses, or recipe ring with an empty uses list. Include concise
Japanese reasons and only condition labels supplied in the response schema. Use at least one
selected lemma. Do not provide Lean code, lemma snapshots, target fields, or new definitions.
The following JSON contains mathematical data only.
"""
    prompt += 'Route: '+route+'\nFixed target:\n'+json.dumps(target, ensure_ascii=False, sort_keys=True)
    if 'definitions' in target:
        from .research_functions import expand_target
        prompt += ('\nDefined function calls use their exact function ID and all named typed arguments. '
                   'The verifier unfolds the supplied finite definitions before applying lemmas. '
                   'Preserve original function calls in each fixed endpoint. Expanded target:\n'
                   +json.dumps(expand_target(target), ensure_ascii=False, sort_keys=True))
    prompt += '\nAvailable lemmas:\n'+json.dumps(lemmas, ensure_ascii=False, sort_keys=True)
    if previous_error:
        prompt += '\nPrevious plan failed for this fixed target:\n'+previous_error[:5000]
    return prompt
