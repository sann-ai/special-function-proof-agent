"""Explicit local research-lemma registration, composition, and sharing."""
import argparse
import json
from pathlib import Path
import sys

from . import research_library as library
from .core import InputError, NeedsConditions, environment, load_json, validate_request, verify
from .parser import parse_identity


def _target(path, conditions):
    raw = path.read_text(encoding='utf-8')
    if path.suffix.lower() == '.json':
        if conditions:
            raise InputError('JSON conditions are fixed in the target.')
        target = load_json(path)
    else:
        target = parse_identity(raw, conditions)
    if not isinstance(target, dict) or 'proof' in target:
        raise InputError('Use a target-only input; the separate research plan supplies its proof.')
    validate_request(target, require_proof=False)
    return target, raw


def _summary(package):
    result = library.read_evidence_json(package, 'result.json')
    return {'id': package['id'], 'name': package['name'], 'saved_status': result['status'],
            'statement': result.get('statement'), 'conditions': result.get('conditions'),
            'environment_matches': result.get('environment') == environment()}


def main(argv=None):
    if argv and argv[0] == 'function':
        from .research_function_cli import main as function_main
        return function_main(argv[1:])
    parser = argparse.ArgumentParser(description='Reuse verified lemmas in new targets; store private research outside this repository.')
    commands = parser.add_subparsers(dest='command', required=True)
    commands.add_parser('function', help='Define finite real research functions; use research function --help.')
    for name in ('add', 'list', 'show', 'reverify', 'export', 'import', 'verify', 'generate'):
        command = commands.add_parser(name)
        command.add_argument('--research-dir', type=Path, help='External library; default ~/SpecialFunctionProofAgentData/research.')
        if name in {'add', 'reverify', 'import', 'verify', 'generate'}:
            command.add_argument('--timeout', type=float, default=240 if name == 'generate' else 60)
        if name == 'add':
            command.add_argument('directory', type=Path)
            command.add_argument('--name', required=True)
            command.add_argument('--source', help='Optional user-supplied citation or URL.')
            command.add_argument('--original-input', type=Path)
        elif name in {'show', 'reverify', 'export'}:
            command.add_argument('identifier')
            if name == 'export':
                command.add_argument('destination', type=Path)
        elif name == 'import':
            command.add_argument('package', type=Path)
            command.add_argument('--reverify', action='store_true', help='Create evidence under the current environment from the fixed saved request.')
        elif name in {'verify', 'generate'}:
            command.add_argument('input', type=Path)
            command.add_argument('--conditions')
            command.add_argument('--using', nargs='+', required=True, metavar='ID')
            command.add_argument('--output', type=Path, required=True)
            command.add_argument('--archive', action='store_true')
            command.add_argument('--archive-dir', type=Path)
            if name == 'verify':
                command.add_argument('--plan', type=Path, required=True, help='Closed plan; selected lemma snapshots are supplied by the verifier.')
            else:
                command.add_argument('--route', choices=['direct', 'steps'], required=True)
                command.add_argument('--model')
                command.add_argument('--attempts', type=int, choices=range(1, 4), default=1)
    args = parser.parse_args(argv)
    if not 0 < getattr(args, 'timeout', 60) <= 600:
        parser.error('--timeout must be positive and at most 600 seconds')
    if getattr(args, 'archive_dir', None) is not None and not args.archive:
        parser.error('--archive-dir requires --archive')
    try:
        root = library.resolve_library_root(args.research_dir)
        if args.command == 'add':
            original = args.original_input.read_text(encoding='utf-8') if args.original_input else None
            package = library.register(args.directory, root, name=args.name, source=args.source,
                                       original_input=original, timeout=args.timeout)
            result = {'id': package['id'], 'name': package['name'], 'status': library.read_evidence_json(package, 'result.json')['status']}
        elif args.command == 'list':
            result = [_summary(package) for package in library.list_entries(root)]
        elif args.command == 'show':
            result = library.load(args.identifier, root)
        elif args.command == 'reverify':
            checked = library.reverify(args.identifier, root, timeout=args.timeout)
            result = {'previous_id': checked['previous_id'], 'id': checked['package']['id'],
                      'status': library.read_evidence_json(checked['package'], 'result.json')['status']}
        elif args.command == 'export':
            result = library.export(args.identifier, args.destination, root)
        elif args.command == 'import':
            if args.reverify:
                checked = library.reverify_package(args.package, root, timeout=args.timeout)
                package = checked['package']
                result = {'previous_id': checked['previous_id'], 'id': package['id'],
                          'status': library.read_evidence_json(package, 'result.json')['status']}
            else:
                package = library.import_package(args.package, root, timeout=args.timeout)
                result = {'id': package['id'], 'name': package['name'],
                          'status': library.read_evidence_json(package, 'result.json')['status']}
        else:
            target, raw = _target(args.input, args.conditions)
            packages = [library.load(identifier, root) for identifier in args.using]
            if args.command == 'generate':
                from .generate import generate
                result = generate(target, args.route, args.output, model=args.model, timeout=args.timeout,
                                  attempts=args.attempts, archive=args.archive, archive_dir=args.archive_dir,
                                  original_input=raw, research_lemmas=packages)
            else:
                from .research_generation import attach_lemmas
                request = {**target, 'proof': attach_lemmas(load_json(args.plan), packages)}
                result = verify(request, args.output, args.timeout)
                if args.archive:
                    from .archive import register_verification
                    record = register_verification(args.output, args.archive_dir, original_input=raw, timeout=args.timeout)
                    result = {**result, 'archive_id': record['id']}
        print(json.dumps(result, ensure_ascii=False, indent=2))
        if args.command in {'verify', 'generate'}:
            return 0 if result.get('status') == 'proved' else 1
        return 0
    except (ValueError, OSError, UnicodeError) as exc:
        print(json.dumps({'status': 'needs_conditions' if isinstance(exc, NeedsConditions) else 'unresolved',
                          'error': str(exc)}, ensure_ascii=False), file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
