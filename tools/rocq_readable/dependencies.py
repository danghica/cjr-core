"""Exact project-reference graph, including references in hidden proofs."""
from __future__ import annotations

from dataclasses import dataclass, field
import bisect

from .ast import identifier, value, walk


def reference_nodes(term):
    """Yield located qualified references, including Ltac's serialized maps."""
    if isinstance(term, dict):
        expr = value(term)
        if isinstance(expr, list) and expr and expr[0] == "Ser_Qualid" and term.get("loc"):
            yield term
        for key, child in term.items():
            if key != "loc":
                yield from reference_nodes(child)
    elif isinstance(term, list):
        if (term and all(isinstance(x, list) and len(x) == 2 and isinstance(x[0], str) for x in term)):
            fields = dict(term)
            expr, raw_loc = fields.get("v"), fields.get("loc")
            if isinstance(expr, list) and expr and expr[0] == "Ser_Qualid" and raw_loc:
                try:
                    loc = dict(raw_loc[0])
                    yield {"v": expr, "loc": {"bp": int(loc["bp"]), "ep": int(loc["ep"])}}
                except (ValueError, TypeError, KeyError, IndexError):
                    pass
        for child in term:
            yield from reference_nodes(child)


def declaration_terms(decl):
    return [decl.reference_ast, decl.context, *decl.proof_spans]


@dataclass
class Graph:
    edges: dict[str, list[str]]
    issues: dict[str, list[str]]
    roots: list[str]
    source_issues: dict[str, list[str]] = field(default_factory=dict)

    @property
    def incomplete(self):
        return any(self.issues.values()) or any(self.source_issues.values())


def root_entries(edges):
    """Return one representative per source strongly connected component."""
    seen, order = set(), []
    reverse = {node: [] for node in edges}
    for node, children in edges.items():
        for child in children:
            reverse[child].append(node)
    for root in sorted(edges):
        pending = [(root, False)]
        while pending:
            node, finished = pending.pop()
            if finished:
                order.append(node)
            elif node not in seen:
                seen.add(node)
                pending.append((node, True))
                pending.extend((child, False) for child in reversed(edges[node]) if child not in seen)
    components, representatives = {}, []
    for root in reversed(order):
        if root in components:
            continue
        component, members, pending = len(representatives), [], [root]
        while pending:
            node = pending.pop()
            if node not in components:
                components[node] = component
                members.append(node)
                pending.extend(reverse[node])
        representatives.append(min(members))
    incoming = {components[child] for node, children in edges.items() for child in children
                if components[node] != components[child]}
    return sorted(rep for i, rep in enumerate(representatives) if i not in incoming)


def build_graph(sources, documents, resolved):
    owners = {d.identity: declaration.identity for source in sources
              for declaration in source.declarations for d in (declaration, *declaration.children)}
    edges, issues = {}, {}
    source_issues = {str(s.relative): ["Source errors may limit dependency coverage."] if s.errors else [] for s in sources}
    project_modules = {s.module for s in sources}
    for source in sources:
        reference_offsets = sorted(source.glob.references)
        for decl, document in zip(source.declarations, documents[source.path]):
            found, warnings = set(), set()
            terms = declaration_terms(decl)
            if source.glob.valid:
                ranges = [(decl.source_start, decl.source_start + len(decl.source.encode()))]
                ranges += [(n["loc"]["bp"], n["loc"]["ep"]) for term in terms[1:]
                           for n in walk(term) if isinstance(n, dict) and n.get("loc")]
                merged = []
                for start, stop in sorted(ranges):
                    if merged and start <= merged[-1][1]:
                        merged[-1] = (merged[-1][0], max(stop, merged[-1][1]))
                    else:
                        merged.append((start, stop))
                offsets = [offset for start, stop in merged
                           for offset in reference_offsets[bisect.bisect_left(reference_offsets, start):bisect.bisect_left(reference_offsets, stop)]
                           if source.glob.references[offset][0] <= stop]
                for offset in offsets:
                    _, identity, kind = source.glob.references[offset]
                    if kind not in ("var", "binder", "lib"):
                        if identity in owners:
                            found.add(owners[identity])
                        elif any(identity.startswith(module + ".") for module in project_modules):
                            warnings.add(f"Project reference has no rendered declaration: {identity}")
            else:
                warnings.add("No fresh .glob: dependencies cover explicit resolved references only; notation and implicit tactic references may be incomplete.")
                # Rendered tokens correctly distinguish global references from
                # locally shadowed binders in statements and context.
                for _, tokens in document.lines():
                    found.update(owners[t.identity] for t in tokens if t.identity in owners and not t.local and not t.anchor)
                proof_locals = {identifier(n) for n in walk([decl.binders, decl.context])
                                if isinstance(value(n), list) and value(n) and value(n)[0] == "Name"}
                for term in terms:
                    in_proof = any(term is span for span in decl.proof_spans)
                    if in_proof:
                        # IntroNaming is encoded as a serialized list in Ltac.
                        # Conservatively retain explicit proof bindings through
                        # the proof rather than treating a homonym as global.
                        for node in walk(term):
                            expr = value(node)
                            if isinstance(expr, list) and len(expr) > 1 and expr[0] in ("IntroIdentifier", "Name"):
                                try:
                                    proof_locals.add(identifier(expr[1]))
                                except ValueError:
                                    pass
                    for node in reference_nodes(term):
                        offset = node["loc"]["bp"]
                        identity = resolved.get(source.path, {}).get(offset)
                        # The adapter handles lexical binders in declarations.
                        # LSP can return a global homonym for a local variable;
                        # use raw resolutions only for hidden proof commands.
                        if in_proof and identifier(node) in proof_locals:
                            continue
                        if identity in owners:
                            if in_proof:
                                found.add(owners[identity])
                        elif source.resolution_status.get(offset) not in ("external", "local"):
                            warnings.add(f"Unresolved reference at byte {offset}: {identifier(node)}")
            if decl.proof_complete is False:
                warnings.add("Proof dependency coverage is incomplete: proof was not fully parsed or was aborted.")
            if source.errors:
                warnings.add("Source errors may limit dependency coverage.")
            edges[decl.identity] = sorted(found)
            issues[decl.identity] = sorted(warnings)
    return Graph(edges, issues, root_entries(edges), source_issues)
