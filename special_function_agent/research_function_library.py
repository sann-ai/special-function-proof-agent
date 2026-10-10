"""Private, explicit packages for typed research function definitions."""
from __future__ import annotations

from copy import deepcopy
from pathlib import Path
import tempfile
from typing import Any

from . import core, research_library as library
from .core import InputError

PACKAGE_KEYS = {'schema_version', 'kind', 'definition', 'source', 'original_input',
                'environment', 'conventions', 'certificate', 'verification', 'id'}
VERIFICATION_KEYS = {'status', 'accepted', 'axioms', 'stdout'}


def resolve_root(root: Path | str | None = None) -> Path:
    """Use the reserved functions subdirectory under an external research root."""
    directory = library._path(library.resolve_library_root(root) / 'functions')
    library._outside_repository(directory)
    if directory.exists() and not directory.is_dir():
        raise InputError('The research function root must be a directory.')
    return directory


def _verification(value: Any) -> dict:
    if not isinstance(value, dict) or set(value) != VERIFICATION_KEYS:
        raise InputError('Function verification needs exactly status, accepted, axioms, and stdout.')
    if value['status'] != 'defined' or value['accepted'] is not True:
        raise InputError('Function definition packages must carry accepted defined status.')
    if not isinstance(value['stdout'], str) or not isinstance(value['axioms'], list):
        raise InputError('Function verification requires its Lean audit output and axiom list.')
    library._text_bytes(value['stdout'])
    axioms = core.audit_axioms(value['stdout'])
    if value['axioms'] != axioms:
        raise InputError('Function verification axioms disagree with its standard audit output.')
    return value


def validate_package(package: Any) -> dict:
    """Check transport integrity and the semantic snapshot without running Lean."""
    from .research_functions import validate_definition
    if not isinstance(package, dict) or set(package) != PACKAGE_KEYS:
        raise InputError('A function package needs exactly the declared package fields.')
    if type(package['schema_version']) is not int or package['schema_version'] != 1:
        raise InputError('Use function package schema_version 1.')
    if package['kind'] != 'function_definition':
        raise InputError('Use the function_definition package kind.')
    for field in ('source', 'original_input'):
        if package[field] is not None:
            library._text_bytes(package[field])
    if (not isinstance(package['environment'], dict) or not package['environment']
            or any(not isinstance(key, str) or not isinstance(value, str)
                   for key, value in package['environment'].items())):
        raise InputError('A function package needs its mathematical environment mapping.')
    if not isinstance(package['conventions'], dict):
        raise InputError('A function package needs its mathematical conventions.')
    library._text_bytes(package['certificate'])
    _verification(package['verification'])
    identifier = package['id']
    if not isinstance(identifier, str) or not library.IDENTIFIER.fullmatch(identifier):
        raise InputError('Use a complete 64-character function package ID.')
    if len(library._json_bytes(package)) + 1 > library.MAX_PACKAGE_BYTES:
        raise InputError('A function package exceeds 256 KiB.')
    validate_definition(package['definition'])
    payload = {key: value for key, value in package.items() if key != 'id'}
    if identifier != library._digest(library._json_bytes(payload)):
        raise InputError('The function package ID does not match its contents.')
    return package


def _read(path: Path | str) -> dict:
    selected = library._path(path)
    if not selected.is_file() or selected.stat().st_size > library.MAX_PACKAGE_BYTES:
        raise InputError('A function package must be a regular JSON file below 256 KiB.')
    try:
        return validate_package(core.load_json(selected))
    except ValueError as exc:
        if isinstance(exc, InputError):
            raise
        raise InputError(f'Invalid function package JSON: {exc}') from exc


def load(identifier: str, root: Path | str | None = None) -> dict:
    if not isinstance(identifier, str) or not library.IDENTIFIER.fullmatch(identifier):
        raise InputError('Select a function package by its complete 64-character ID.')
    package = _read(resolve_root(root) / (identifier + '.json'))
    if package['id'] != identifier:
        raise InputError('The function filename and package ID disagree.')
    return package


def list_entries(root: Path | str | None = None) -> list[dict]:
    directory = resolve_root(root)
    if not directory.exists():
        return []
    result = []
    for path in sorted(directory.iterdir()):
        if path.suffix != '.json' or not library.IDENTIFIER.fullmatch(path.stem):
            raise InputError('The functions directory may contain only ID-named JSON packages.')
        result.append(load(path.stem, root))
    return result


def _current_source(package: dict) -> str:
    from .research_functions import definition_conventions, render_definition
    validate_package(package)
    if (package['environment'] != core.environment()
            or package['conventions'] != definition_conventions(package['definition'])):
        raise InputError('The function mathematical environment or conventions changed; use explicit reverification.')
    source = render_definition(package['definition'])
    if package['certificate'] != source:
        raise InputError('The function certificate differs from its regenerated definition.')
    return source


def definitions(packages: list[dict]) -> list[dict]:
    """Select current semantic snapshots by package IDs, preserving their dependency closure."""
    from .research_functions import MAX_DEFINITIONS, metadata
    if not isinstance(packages, list) or not 1 <= len(packages) <= MAX_DEFINITIONS:
        raise InputError('Select one to twelve function definition packages.')
    identifiers, result = set(), []
    for package in packages:
        _current_source(package)
        snapshot = package['definition']
        if snapshot['id'] in identifiers:
            raise InputError('Selected function definition IDs must be distinct.')
        identifiers.add(snapshot['id'])
        result.append(deepcopy(snapshot))
    metadata(result)  # Enforce the shared closure and depth bounds across all selections.
    return result


def _check(source: str, timeout: float) -> dict:
    with tempfile.TemporaryDirectory(prefix='special-function-definition-') as temporary:
        certificate = Path(temporary) / 'definition.lean'
        certificate.write_text(source, encoding='utf-8')
        checked = core._run_lean(certificate, timeout)
    if checked.get('accepted') is not True:
        raise InputError('The generated function definition did not pass Lean: '+str(checked.get('reason', 'rejected')))
    verification = {'status': 'defined', 'accepted': True, 'axioms': checked.get('axioms'),
                    'stdout': checked.get('stdout')}
    return _verification(verification)


def _make_package(snapshot: dict, *, source: str | None, original_input: str | None,
                  timeout: float) -> dict:
    from .research_functions import definition_conventions, render_definition, validate_definition
    snapshot = deepcopy(snapshot)
    validate_definition(snapshot)
    for text in (source, original_input):
        if text is not None:
            library._text_bytes(text)
    environment = core.environment()
    conventions = definition_conventions(snapshot)
    generated = render_definition(snapshot)
    payload = {'schema_version': 1, 'kind': 'function_definition', 'definition': snapshot,
               'source': source, 'original_input': original_input, 'environment': environment,
               'conventions': conventions, 'certificate': generated}
    if len(library._json_bytes(payload)) > library.MAX_PACKAGE_BYTES:
        raise InputError('A function package exceeds 256 KiB.')
    verification = _check(generated, timeout)
    if environment != core.environment() or conventions != definition_conventions(snapshot):
        raise InputError('The mathematical environment changed during function verification.')
    package = {**payload, 'verification': verification}
    package['id'] = library._digest(library._json_bytes(package))
    return validate_package(package)


def _store(package: dict, root: Path | str | None) -> dict:
    directory = resolve_root(root)
    destination = directory / (package['id'] + '.json')
    if destination.exists() or destination.is_symlink():
        existing = load(package['id'], root)
        if existing != package:
            raise InputError('An existing function package has different contents.')
        return existing
    directory.mkdir(parents=True, exist_ok=True, mode=0o700)
    library._write(destination, package)
    return package


def register(rawDefinition: dict, root: Path | str | None = None, *, source: str | None = None,
             original_input: str | None = None, timeout: float = 60) -> dict:
    from .research_functions import make_definition
    resolve_root(root)
    snapshot = make_definition(deepcopy(rawDefinition))
    package = _make_package(snapshot, source=source, original_input=original_input, timeout=timeout)
    return _store(package, root)


def export(identifier: str, destination: Path | str, root: Path | str | None = None) -> dict:
    package = load(identifier, root)
    path = library._path(destination)
    library._outside_repository(path)
    path.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
    library._write(path, package)
    return {'id': package['id'], 'definition_id': package['definition']['id'], 'path': str(path)}


def import_package(path: Path | str, root: Path | str | None = None, timeout: float = 60) -> dict:
    resolve_root(root)
    package = _read(path)
    source = _current_source(package)
    _check(source, timeout)
    _current_source(package)  # Refuse a concurrent environment change before committing a record.
    return _store(package, root)


def _reverify(package: dict, root: Path | str | None, timeout: float) -> dict:
    resolve_root(root)
    updated = _make_package(package['definition'], source=package['source'],
                            original_input=package['original_input'], timeout=timeout)
    if updated['definition'] != package['definition']:
        raise InputError('Reverification must preserve the exact semantic definition snapshot.')
    _store(updated, root)
    return {'previous_id': package['id'], 'package': updated}


def reverify(identifier: str, root: Path | str | None = None, timeout: float = 60) -> dict:
    return _reverify(load(identifier, root), root, timeout)


def reverify_package(path: Path | str, root: Path | str | None = None, timeout: float = 60) -> dict:
    return _reverify(_read(path), root, timeout)
