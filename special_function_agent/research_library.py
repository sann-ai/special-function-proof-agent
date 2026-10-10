"""Explicit, content-addressed research packages with verifier-owned certificates."""
from __future__ import annotations

from copy import deepcopy
import hashlib
import json
import math
import os
from pathlib import Path
import re
import tempfile
from typing import Any

from . import core
from .archive import VERIFICATION_FILES
from .core import InputError

MAX_PACKAGE_BYTES = 256 * 1024
PACKAGE_KEYS = {'schema_version', 'name', 'source', 'original_input', 'evidence', 'manifest', 'id'}
IDENTIFIER = re.compile(r'[a-f0-9]{64}\Z')
NAME = re.compile(r'[A-Za-z][A-Za-z0-9_-]{0,63}\Z')
STATES = {'proved', 'refuted', 'unresolved', 'needs_conditions'}


def _json_bytes(value: Any) -> bytes:
    try:
        return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(',', ':'),
                          allow_nan=False).encode('utf-8')
    except (TypeError, ValueError, UnicodeEncodeError, RecursionError) as exc:
        raise InputError('Research packages must contain finite UTF-8 JSON values.') from exc


def _text_bytes(value: Any) -> bytes:
    if not isinstance(value, str):
        raise InputError('Research evidence must be UTF-8 text.')
    try:
        return value.encode('utf-8')
    except UnicodeEncodeError as exc:
        raise InputError('Research evidence must be UTF-8 text.') from exc


def _digest(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _strict_json(text: str) -> Any:
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise InputError(f'Duplicate JSON key: {key}')
            result[key] = value
        return result

    def constant(value):
        raise InputError(f'Non-finite JSON constants are unsupported: {value}')

    def finite_float(value):
        result = float(value)
        if not math.isfinite(result):
            raise InputError(f'Non-finite JSON numbers are unsupported: {value}')
        return result

    try:
        value = json.loads(text, object_pairs_hook=unique, parse_constant=constant,
                           parse_float=finite_float)
        _json_bytes(value)  # Escaped JSON strings must also decode to valid UTF-8 text.
        return value
    except (ValueError, RecursionError) as exc:
        raise InputError(f'Invalid evidence JSON: {exc}') from exc


def validate_package(package: Any) -> dict:
    """Check the closed transport format, without replay or environment assumptions."""
    if not isinstance(package, dict) or set(package) != PACKAGE_KEYS:
        raise InputError('A research package needs exactly the declared package fields.')
    if type(package['schema_version']) is not int or package['schema_version'] != 1:
        raise InputError('Use research package schema_version 1.')
    if not isinstance(package['name'], str) or not NAME.fullmatch(package['name']):
        raise InputError('Use an ASCII research name of 1–64 letters, digits, hyphens, or underscores, starting with a letter.')
    for key in ('source', 'original_input'):
        if package[key] is not None:
            _text_bytes(package[key])
    evidence, manifest = package['evidence'], package['manifest']
    if (not isinstance(evidence, dict) or not {'request.json', 'result.json'} <= set(evidence)
            or set(evidence) - VERIFICATION_FILES):
        raise InputError('Research evidence must use the fixed verification filenames, including request.json and result.json.')
    if not isinstance(manifest, dict) or set(manifest) != set(evidence):
        raise InputError('The research manifest must describe exactly every evidence file.')
    for name, text in evidence.items():
        raw = _text_bytes(text)
        if len(raw) > MAX_PACKAGE_BYTES:
            raise InputError('Research evidence exceeds 256 KiB.')
        digest = manifest[name]
        if not isinstance(digest, str) or not IDENTIFIER.fullmatch(digest) or digest != _digest(raw):
            raise InputError(f'Research evidence changed: {name}')
        if name.endswith('.json'):
            _strict_json(text)
    identifier = package['id']
    if not isinstance(identifier, str) or not IDENTIFIER.fullmatch(identifier):
        raise InputError('Use a complete 64-character research package ID.')
    if identifier != _digest(_json_bytes({key: value for key, value in package.items() if key != 'id'})):
        raise InputError('The research package ID does not match its contents.')
    if len(_json_bytes(package)) + 1 > MAX_PACKAGE_BYTES:
        raise InputError('A research package exceeds 256 KiB.')
    return package


def read_evidence_json(package: dict, filename: str) -> dict:
    """Read strict JSON from a validated in-memory snapshot without running Lean."""
    validate_package(package)
    if (not isinstance(filename, str) or filename not in VERIFICATION_FILES
            or not filename.endswith('.json') or filename not in package['evidence']):
        raise InputError('Choose a JSON file present in the research evidence.')
    value = _strict_json(package['evidence'][filename])
    if not isinstance(value, dict):
        raise InputError(f'Research evidence {filename} must contain an object.')
    return value


def _path(path: Path | str) -> Path:
    chosen = Path(path).expanduser()
    if chosen.is_symlink():
        raise InputError('Research paths cannot be symbolic links.')
    return chosen.resolve()


def _outside_repository(path: Path) -> None:
    if path == core.ROOT.resolve() or core.ROOT.resolve() in path.parents:
        raise InputError('Research packages must be stored outside the application repository.')


def resolve_library_root(root: Path | str | None = None) -> Path:
    chosen = root if root is not None else os.environ.get('SPECIAL_FUNCTION_RESEARCH_DIR')
    path = _path(chosen if chosen else Path.home() / 'SpecialFunctionProofAgentData' / 'research')
    _outside_repository(path)
    if path.exists() and not path.is_dir():
        raise InputError('The research library root must be a directory.')
    return path


def _state(package: dict) -> tuple[dict, dict]:
    request = read_evidence_json(package, 'request.json')
    result = read_evidence_json(package, 'result.json')
    if type(request.get('schema_version')) is not int or request['schema_version'] != 2:
        raise InputError('Research packages support version 2 requests; use the evidence archive for version 1.')
    if not isinstance(result.get('status'), str) or result['status'] not in STATES:
        raise InputError('Research status must be proved, refuted, unresolved, or needs_conditions.')
    conditional = result.get('conditional_lean', {})
    if not isinstance(conditional, dict) or ('accepted' in conditional and type(conditional['accepted']) is not bool):
        raise InputError('Invalid conditional research evidence status.')
    for flag in ('full_function_proof', 'full_bessel_proof'):
        if flag in result and type(result[flag]) is not bool:
            raise InputError('Research full-proof flags must be booleans.')
        if result['status'] != 'proved' and result.get(flag) is True:
            raise InputError('An unresolved or conditional record cannot carry full-proof scope.')
    if result['status'] == 'proved' and result.get('full_function_proof') is not True:
        raise InputError('A proved version 2 package requires a full function certificate.')
    if result['status'] in {'proved', 'refuted'}:
        if 'certificate.lean' not in package['evidence'] or conditional.get('accepted'):
            raise InputError('Accepted research records need their full certificate and matching scope.')
    elif conditional.get('accepted') and 'conditional_certificate.lean' not in package['evidence']:
        raise InputError('A conditional research record needs its conditional certificate.')
    return request, result


def _read(path: Path) -> dict:
    path = _path(path)
    if not path.is_file() or path.stat().st_size > MAX_PACKAGE_BYTES:
        raise InputError('A research package must be a regular JSON file below 256 KiB.')
    try:
        package = validate_package(core.load_json(path))
    except ValueError as exc:
        if isinstance(exc, InputError):
            raise
        raise InputError(f'Invalid research package JSON: {exc}') from exc
    _state(package)
    return package


def load(identifier: str, root: Path | str | None = None) -> dict:
    if not isinstance(identifier, str) or not IDENTIFIER.fullmatch(identifier):
        raise InputError('Select research evidence by its complete 64-character ID.')
    directory = resolve_library_root(root)
    package = _read(directory / (identifier + '.json'))
    if package['id'] != identifier:
        raise InputError('The research filename and package ID disagree.')
    return package


def list_entries(root: Path | str | None = None) -> list[dict]:
    directory = resolve_library_root(root)
    if not directory.exists():
        return []
    result = []
    for path in sorted(directory.iterdir()):
        if path.suffix != '.json' or not IDENTIFIER.fullmatch(path.stem):
            raise InputError('A research library may contain only ID-named JSON packages.')
        result.append(load(path.stem, directory))
    return result


def _write(path: Path, package: dict) -> None:
    try:
        with path.open('xb') as stream:
            os.chmod(path, 0o600)
            stream.write(_json_bytes(package) + b'\n')
            stream.flush()
            os.fsync(stream.fileno())
    except FileExistsError as exc:
        raise InputError('Research exports and records cannot overwrite existing files.') from exc


def _store(package: dict, root: Path | str | None) -> dict:
    directory = resolve_library_root(root)
    destination = directory / (package['id'] + '.json')
    if destination.exists() or destination.is_symlink():
        existing = load(package['id'], directory)
        if existing != package:
            raise InputError('An existing research record has different contents.')
        return existing
    directory.mkdir(parents=True, exist_ok=True, mode=0o700)
    _write(destination, package)
    return package


def _replay_accepted(package: dict, timeout: float) -> None:
    _, result = _state(package)
    accepted = result['status'] in {'proved', 'refuted'}
    conditional = result.get('conditional_lean', {}).get('accepted') is True
    if not accepted and not conditional:
        return
    with tempfile.TemporaryDirectory(prefix='special-function-research-replay-') as temporary:
        directory = Path(temporary)
        for name, text in package['evidence'].items():
            (directory / name).write_bytes(_text_bytes(text))
        # Replay regenerates the source from the fixed request before Lean sees any file.
        checked = core.replay(directory, timeout)
    if accepted:
        if checked.get('replayed') is not True or checked.get('status') != result['status']:
            raise InputError('The research certificate did not pass replay.')
    elif (checked.get('conditional_replayed') is not True or checked.get('full_bessel_proof') is not False
          or checked.get('replayed') is not False or checked.get('status') != result['status']):
        raise InputError('The conditional research certificate did not pass replay in its original scope.')


def _snapshot(verification_dir: Path | str, *, name: str, source: str | None,
              original_input: str | None) -> dict:
    directory = _path(verification_dir)
    if not directory.is_dir():
        raise InputError('Choose a verification directory to register.')
    evidence = {}
    for path in sorted(directory.iterdir()):
        if path.name not in VERIFICATION_FILES or path.is_symlink() or not path.is_file():
            raise InputError('Verification evidence must contain only allowlisted regular files.')
        if path.stat().st_size > MAX_PACKAGE_BYTES:
            raise InputError('Research evidence exceeds 256 KiB.')
        try:
            evidence[path.name] = path.read_bytes().decode('utf-8')
        except UnicodeDecodeError as exc:
            raise InputError('Research evidence must be UTF-8 text.') from exc
    package = {'schema_version': 1, 'name': name, 'source': source, 'original_input': original_input,
               'evidence': evidence, 'manifest': {key: _digest(_text_bytes(value)) for key, value in evidence.items()}}
    package['id'] = _digest(_json_bytes(package))
    validate_package(package)
    _state(package)
    return package


def register(verification_dir: Path | str, library_root: Path | str | None = None, *,
             name: str, source: str | None = None, original_input: str | None = None,
             timeout: float = 60) -> dict:
    resolve_library_root(library_root)
    package = _snapshot(verification_dir, name=name, source=source, original_input=original_input)
    _replay_accepted(package, timeout)
    return _store(package, library_root)


def export(identifier: str, destination: Path | str, root: Path | str | None = None) -> dict:
    package = load(identifier, root)
    path = _path(destination)
    _outside_repository(path)
    path.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
    _write(path, package)
    return {'id': package['id'], 'path': str(path)}


def import_package(path: Path | str, root: Path | str | None = None, timeout: float = 60) -> dict:
    resolve_library_root(root)
    package = _read(Path(path))
    _replay_accepted(package, timeout)
    return _store(package, root)


def _dependency_closure(package: dict) -> tuple[dict[str, dict], list[str]]:
    from .research_proof import MAX_DEPTH, MAX_PACKAGES, is_research
    packages, active, order, heights = {}, set(), [], {}

    def visit(snapshot, depth):
        validate_package(snapshot)
        key = snapshot['id']
        if depth > MAX_DEPTH or key in active:
            raise InputError('Research dependencies exceed the depth limit or contain a cycle.')
        if key in packages:
            if depth + heights[key] - 1 > MAX_DEPTH:
                raise InputError('Research dependencies exceed the depth limit.')
            return
        if len(packages) >= MAX_PACKAGES:
            raise InputError('At most twelve research packages may occur in the dependency closure.')
        packages[key] = snapshot
        height = 1
        active.add(key)
        request, result = _state(snapshot)
        if depth > 1 and (result['status'] != 'proved' or result.get('full_function_proof') is not True):
            raise InputError('Research dependencies must retain full-proof scope.')
        if is_research(request):
            proof = request['proof']
            if proof.get('mode') == 'direct':
                core._keys(proof, {'mode', 'recipe', 'uses', 'lemmas'})
                uses = [proof['uses']]
            elif proof.get('mode') == 'steps':
                core._keys(proof, {'mode', 'steps', 'lemmas'})
                if not isinstance(proof['steps'], list):
                    raise InputError('Research steps must be a list.')
                uses = []
                for step in proof['steps']:
                    core._keys(step, {'before', 'after', 'recipe', 'uses', 'reason', 'conditions'})
                    uses.append(step['uses'])
            else:
                raise InputError('Research proof mode must be direct or steps.')
            children = proof['lemmas']
            if not isinstance(children, list) or not 1 <= len(children) <= MAX_PACKAGES:
                raise InputError('A research proof needs one to twelve package snapshots.')
            child_ids = set()
            for child in children:
                validate_package(child)
                if child['id'] in child_ids:
                    raise InputError('Research package IDs must be distinct.')
                child_ids.add(child['id'])
            for group in uses:
                if not isinstance(group, list):
                    raise InputError('Research lemma uses must be a list.')
                for use in group:
                    core._keys(use, {'lemma', 'arguments', 'reverse'})
                    if not isinstance(use['lemma'], str) or use['lemma'] not in child_ids:
                        raise InputError('Each research use must select an embedded package ID.')
            for child in children:
                visit(child, depth + 1)
                height = max(height, heights[child['id']] + 1)
        active.remove(key)
        heights[key] = height
        order.append(key)

    visit(package, 1)
    return packages, order


def _reverify(package: dict, root: Path | str | None, timeout: float) -> dict:
    resolve_library_root(root)
    packages, order = _dependency_closure(package)
    refreshed = {}
    with tempfile.TemporaryDirectory(prefix='special-function-research-verify-') as temporary:
        for key in order:
            previous = packages[key]
            request, _ = _state(previous)
            request = deepcopy(request)
            proof = request.get('proof', {})
            if 'lemmas' in proof:
                replacements = {child['id']: refreshed[child['id']] for child in proof['lemmas']}
                proof['lemmas'] = [replacements[child['id']] for child in proof['lemmas']]
                groups = [proof['uses']] if proof['mode'] == 'direct' else [step['uses'] for step in proof['steps']]
                for group in groups:
                    for use in group:
                        use['lemma'] = replacements[use['lemma']]['id']
            directory = Path(temporary) / key
            result = core.verify(request, directory, timeout)
            if len(packages) > 1 and (result.get('status') != 'proved' or result.get('full_function_proof') is not True):
                raise InputError(f'Research dependency reverification did not prove package {key}: {result.get("reason", result.get("status"))}')
            refreshed[key] = _snapshot(directory, name=previous['name'], source=previous['source'],
                                       original_input=previous['original_input'])
        updated = refreshed[package['id']]
        _replay_accepted(updated, timeout)
        _store(updated, root)
    return {'previous_id': package['id'], 'package': updated}


def reverify(identifier: str, root: Path | str | None = None, timeout: float = 60) -> dict:
    """Regenerate one saved request in the current environment, preserving its proof mode."""
    return _reverify(load(identifier, root), root, timeout)


def reverify_package(path: Path | str, root: Path | str | None = None, timeout: float = 60) -> dict:
    """Explicitly reverify a selected external package without executing its Lean text."""
    return _reverify(_read(Path(path)), root, timeout)
