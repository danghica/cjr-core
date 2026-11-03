"""Statement-only implementation/specification bridges with reviewed main entries."""
from __future__ import annotations

import json
import re

from .ast import identifier, value, walk
from .dependencies import reference_nodes


def classify_contracts(sources, documents, resolved, statement_edges):
    declarations = {d.identity: (s, d) for s in sources for d in s.declarations}
    specs = {i for i, (s, _) in declarations.items() if 'spec' in s.relative.parts}
    implementations = {i for i, (s, d) in declarations.items() if d.body and
                       ('algorithm' in s.relative.parts or i in s.cangjie)}
    representations = {i for i, (s, d) in declarations.items() if d.body and d.type and
                       re.search(r'\biProp\b', s.fragment(d.type))}

    def closure(roots):
        seen, pending = set(), list(roots)
        while pending:
            identity = pending.pop()
            if identity in seen:
                continue
            seen.add(identity)
            # A theorem's proof is never traversed; these edges come only
            # from the rendered statement or a definition's body and binders.
            pending.extend(statement_edges.get(identity, []))
        return seen

    roots = {s.root for s in sources}
    selected = set()
    for root in roots:
        config = root / 'project.config.json'
        if config.is_file():
            configured = json.loads(config.read_text()).get('main_correctness_contracts', [])
            if not isinstance(configured, list) or any(not isinstance(i, str) for i in configured):
                raise ValueError('main_correctness_contracts must be a list of qualified declaration identities')
            selected.update(configured)

    records = {}
    for source in sources:
        for decl, document in zip(source.declarations, documents[source.path]):
            if source.errors or decl.proof_complete is False or decl.body or not decl.type or decl.kind not in {'lemma', 'theorem', 'corollary', 'proposition', 'fact', 'remark'}:
                continue
            globals_ = {t.identity for _, tokens in document.lines() for t in tokens
                        if t.identity in declarations and not t.local and not t.anchor}
            locals_ = {identifier(n) for n in walk([decl.binders, decl.context])
                       if isinstance(value(n), list) and value(n) and value(n)[0] == 'Name'}

            def identity(node):
                if not isinstance(node, dict):
                    return None
                offset = (node.get('loc') or {}).get('bp')
                ref = source.glob.references.get(offset) if source.glob.valid else None
                if ref:
                    found = ref[1] if ref[2] not in {'var', 'binder', 'lib'} else None
                else:
                    found = resolved.get(source.path, {}).get(offset)
                    if identifier(node) in locals_:
                        return None
                    if not found:
                        matches = [i for i in globals_ if i == identifier(node) or i.rsplit('.', 1)[-1] == identifier(node)]
                        found = matches[0] if len(matches) == 1 else None
                return found if found in globals_ else None

            def references(term):
                return {i for n in reference_nodes(term) if (i := identity(n))}

            def head(term):
                expr = value(term)
                if not isinstance(expr, list) or not expr:
                    return None
                if expr[0] == 'CApp':
                    return head(expr[1])
                if expr[0] == 'CRef':
                    return identity(expr[1])
                if expr[0] == 'CAppExpl':
                    return identity(expr[1][0])
                if expr[0] in {'CDelimiters', 'CCast'}:
                    return head(expr[-1] if expr[0] == 'CDelimiters' else expr[1])
                return None

            operations, specification, reps = set(), set(), set()
            for node in walk(decl.type):
                expr = value(node)
                if not isinstance(expr, list) or len(expr) < 4 or expr[0] != 'CNotation' or not expr[2][1].startswith('WP '):
                    continue
                terms = expr[3][0]
                if len(terms) < 3:
                    continue
                ops = {op for term in terms[:-2] if (op := head(term)) in implementations}
                post_refs = references(terms[-1])
                reachable = closure(post_refs)
                if ops and reachable & specs:
                    operations.update(ops)
                    specification.update(reachable & specs)
                    reps.update(reachable & representations)
            if not operations:
                continue
            related = operations | reps | specification
            main = decl.identity in selected
            records[decl.identity] = {
                'main': main, 'selection': 'project annotation' if main else 'detected candidate',
                'operations': sorted(operations), 'specifications': sorted(specification),
                'representations': sorted(reps), 'related': sorted(related),
                'reason': 'The WP statement connects a named CJR operation to specification definitions in its postcondition.'}
    return records
