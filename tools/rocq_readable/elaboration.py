"""Read-only, isolated elaboration in the declaration's live Rocq environment."""
from __future__ import annotations

import json
from .backend import BackendError
from .gallina import request

PREFIX = 'ROCQ-READABLE-JSON:'


def statement(source, decl):
    """Retain the original binder grammar, including generalized typeclasses."""
    name_end = (decl.name_node.get('loc') or {}).get('ep')
    type_start = (decl.type.get('loc') or {}).get('bp') if isinstance(decl.type, dict) else None
    if name_end is None or type_start is None:
        raise ValueError('Declaration has no source range for its signature.')
    binders = source.text.encode()[name_end:type_start].decode().strip()
    if binders.endswith(':'):
        binders = binders[:-1].strip()
    text = source.fragment(decl.type)
    return ('forall ' + binders + ', ' if binders else '') + text


def export(backend, source, unavailable=None):
    for decl in source.declarations:
        record = {'status': 'unavailable', 'reason': unavailable or '', 'unsupported': []}
        source.elaborated[decl.identity] = record
        if unavailable:
            continue
        try:
            if decl.unsupported:
                raise ValueError('This declaration form retains its source rendering.')
            if decl.body is None and decl.type is not None and not decl.children:
                command = 'Readable Type (' + statement(source, decl) + ').'
                offset = decl.source_start
            else:
                command = 'Readable ' + ('Definition ' if decl.body is not None else 'Signature ') + decl.name + '.'
                offset = decl.source_start + len(decl.source.encode())
            response = request(backend, source, command, offset)
            messages = [str(item[1]).strip() for item in response.get('feedback', [])
                        if isinstance(item, list) and len(item) == 2]
            payloads = [m[len(PREFIX):] for m in messages if m.startswith(PREFIX)]
            if len(payloads) != 1:
                raise ValueError('The Rocq exporter returned no elaborated term.')
            data = json.loads(payloads[0])
            if data.get('version') != 1 or not isinstance(data.get('type'), dict) or not isinstance(data.get('context'), list):
                raise ValueError('Unsupported elaborated-term protocol.')
            record.update(status='available', reason='', term=data)
            # Constructors and fields remain distinct declarations in the details.
            if decl.children:
                children = []
                for child in decl.children:
                    reply = request(backend, source, 'Readable Signature ' + child.name + '.', offset)
                    for _, message in reply.get('feedback', []):
                        if str(message).startswith(PREFIX):
                            children.append({'identity': child.identity, 'term': json.loads(str(message)[len(PREFIX):])})
                record['children'] = children
        except (BackendError, ValueError, KeyError, TypeError) as exc:
            record.update(status='unavailable', reason=str(exc), term=None)
