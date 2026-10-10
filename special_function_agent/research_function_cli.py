"""Explicit finite function definitions in the private research directory."""
import argparse
import json
from pathlib import Path
import sys

from . import research_function_library as library
from .core import InputError, NeedsConditions, load_json, validate_request, verify


def main(argv=None):
    parser = argparse.ArgumentParser(description='Define finite real research functions, then prove fixed targets using their definitions.')
    commands = parser.add_subparsers(dest='command', required=True)
    for name in ('add', 'list', 'show', 'reverify', 'export', 'import', 'verify', 'generate'):
        command = commands.add_parser(name)
        command.add_argument('--research-dir', type=Path)
        if name in {'add', 'reverify', 'import', 'verify', 'generate'}:
            command.add_argument('--timeout', type=float, default=240 if name == 'generate' else 60)
        if name == 'add':
            command.add_argument('definition', type=Path)
            command.add_argument('--source', help='User-supplied citation or URL.')
        elif name in {'show', 'reverify', 'export'}:
            command.add_argument('identifier')
            if name == 'export':
                command.add_argument('destination', type=Path)
        elif name == 'import':
            command.add_argument('package', type=Path)
            command.add_argument('--reverify', action='store_true')
        elif name in {'verify', 'generate'}:
            command.add_argument('input', type=Path, help='Fixed target JSON without definitions or proof; selected definitions are attached by the verifier.')
            command.add_argument('--using', nargs='+', required=True, metavar='FUNCTION_PACKAGE_ID')
            command.add_argument('--route', choices=['direct', 'steps'], required=True)
            command.add_argument('--output', type=Path, required=True)
            command.add_argument('--archive', action='store_true')
            command.add_argument('--archive-dir', type=Path)
            if name == 'generate':
                command.add_argument('--model')
                command.add_argument('--attempts', type=int, choices=range(1, 4), default=1)
    args = parser.parse_args(argv)
    if not 0 < getattr(args, 'timeout', 60) <= 600:
        parser.error('--timeout must be positive and at most 600 seconds')
    if getattr(args, 'archive_dir', None) is not None and not args.archive:
        parser.error('--archive-dir requires --archive')
    try:
        root = args.research_dir
        if args.command == 'add':
            package = library.register(load_json(args.definition), root, source=args.source,
                                       original_input=args.definition.read_text(encoding='utf-8'), timeout=args.timeout)
            result = {'id': package['id'], 'definition_id': package['definition']['id'], 'status': 'defined'}
        elif args.command == 'list':
            result = [{'id': p['id'], 'definition_id': p['definition']['id'],
                       'name': p['definition']['name'], 'status': 'defined'} for p in library.list_entries(root)]
        elif args.command == 'show':
            result = library.load(args.identifier, root)
        elif args.command == 'export':
            result = library.export(args.identifier, args.destination, root)
        elif args.command in {'reverify', 'import'}:
            if args.command == 'reverify' or args.reverify:
                checked = (library.reverify(args.identifier, root, timeout=args.timeout) if args.command == 'reverify'
                           else library.reverify_package(args.package, root, timeout=args.timeout))
                package = checked['package']
                result = {'previous_id': checked['previous_id'], 'id': package['id'],
                          'definition_id': package['definition']['id'], 'status': 'defined'}
            else:
                package = library.import_package(args.package, root, timeout=args.timeout)
                result = {'id': package['id'], 'definition_id': package['definition']['id'], 'status': 'defined'}
        else:
            raw = args.input.read_text(encoding='utf-8')
            target = load_json(args.input)
            if not isinstance(target, dict) or {'definitions', 'proof'} & target.keys():
                raise InputError('The input fixes the target; the verifier attaches the selected definitions and proof.')
            packages = [library.load(key, root) for key in args.using]
            target = {**target, 'definitions': library.definitions(packages)}
            validate_request(target, require_proof=False)
            if args.command == 'generate':
                from .generate import generate
                result = generate(target, args.route, args.output, model=args.model, timeout=args.timeout,
                                  attempts=args.attempts, archive=args.archive, archive_dir=args.archive_dir,
                                  original_input=raw)
            else:
                from .defined_proof import default_proof
                result = verify({**target, 'proof': default_proof(target, args.route)}, args.output, args.timeout)
                if args.archive:
                    from .archive import register_verification
                    record = register_verification(args.output, args.archive_dir, original_input=raw, timeout=args.timeout)
                    result = {**result, 'archive_id': record['id']}
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return 0 if args.command not in {'verify', 'generate'} or result.get('status') == 'proved' else 1
    except (ValueError, OSError, UnicodeError) as exc:
        print(json.dumps({'status': 'needs_conditions' if isinstance(exc, NeedsConditions) else 'unresolved',
                          'error': str(exc)}, ensure_ascii=False), file=sys.stderr)
        return 2
