"""Coq 8.20 concrete AST adapter. Unsupported syntax stays visibly intact."""
from __future__ import annotations

from dataclasses import dataclass, field
import bisect
import json

from .layout import Doc, Token, anchor, leaf


def value(node):
    return node.get("v") if isinstance(node, dict) else node


def identifier(node):
    node = value(node)
    if isinstance(node, list):
        if node[0] == "Id":
            return node[1]
        if node[0] == "Name":
            return identifier(node[1])
        if node[0] == "Anonymous":
            return "_"
        if node[0] == "Ser_Qualid":
            return ".".join([*(identifier(x) for x in reversed(node[1][1])), identifier(node[2])])
    raise ValueError(f"unknown identifier shape: {node!r}")


def walk(node):
    yield node
    if isinstance(node, dict):
        for key, child in node.items():
            if key != "loc":
                yield from walk(child)
    elif isinstance(node, list):
        for child in node:
            yield from walk(child)


@dataclass
class Declaration:
    name: str
    identity: str
    kind: str
    name_node: dict
    source: str
    source_start: int = 0
    binders: list = field(default_factory=list)
    body: dict | None = None
    type: dict | None = None
    context: list = field(default_factory=list)
    children: list = field(default_factory=list)
    section: str = ""
    metadata: list = field(default_factory=list)
    unsupported: bool = False
    reference_ast: dict | None = None
    proof_spans: list = field(default_factory=list)
    proof_complete: bool | None = None


def declarations(source, document):
    modules, segments, context = [], [], []
    proof = False
    proof_owners = []

    def declaration(name_node, kind, ast, **kwargs):
        name = identifier(name_node)
        start = (name_node.get("loc") or {}).get("bp", -1)
        identity = source.glob.definitions.get(start, (".".join([source.module, *modules, name]), ""))[0]
        return Declaration(name, identity, kind, name_node, source.fragment(ast),
                           source_start=(ast.get("loc") or {}).get("bp", 0),
                           context=list(context), section=" / ".join(s[0] for s in segments),
                           reference_ast=ast, **kwargs)

    for span in document.get("spans", []):
        ast = span.get("ast")
        if not ast:
            continue
        expression = ast["v"]["expr"][1]
        tag, *args = expression
        if tag in ("VernacEndProof", "VernacAbort", "VernacAbortAll"):
            for owner in proof_owners:
                owner.proof_spans.append(ast)
                owner.proof_complete = tag == "VernacEndProof"
            proof_owners = []
            proof = False
            continue
        if proof:
            for owner in proof_owners:
                owner.proof_spans.append(ast)
            continue
        previous_count = len(source.declarations)
        if tag in ("VernacBeginSection", "VernacDefineModule", "VernacDeclareModule"):
            name_node = args[0] if tag == "VernacBeginSection" else args[1]
            name = identifier(name_node)
            segments.append((name, len(context), len(modules)))
            if tag != "VernacBeginSection":
                modules.append(name)
            continue
        if tag == "VernacEndSegment":
            if segments:
                _, context_len, modules_len = segments.pop()
                del context[context_len:]
                del modules[modules_len:]
            continue
        if tag == "VernacContext":
            context.extend(args[0])
            continue
        if tag == "VernacAssumption":
            for coercion, (names, type_) in args[2]:
                for name_decl in names:
                    name_node = name_decl[0]
                    lname = {**name_node, "v": ["Name", value(name_node)]}
                    binder = ["CLocalAssum", [lname], None, ["Default", ["Explicit"]], type_]
                    if segments and args[0][0][0] == "DoDischarge":
                        context.append(binder)
                    else:
                        source.declarations.append(declaration(name_node, "assumption", ast, type=type_))
            continue
        if tag == "VernacDefinition":
            name_decl, definition = args[1:]
            kind = args[0][1][0].lower()
            if definition[0] == "DefineBody":
                _, binders, reduction, body, type_ = definition
                decl = declaration(name_decl[0], kind, ast, binders=binders, body=body, type=type_)
                if reduction is not None or name_decl[1] is not None:
                    decl.metadata.append(source.fragment(ast).split(":=", 1)[0])
            else:
                _, binders, type_ = definition
                decl = declaration(name_decl[0], kind, ast, binders=binders, type=type_)
                proof = True
            source.declarations.append(decl)
        elif tag == "VernacStartTheoremProof":
            for name_decl, (binders, type_) in args[1]:
                source.declarations.append(declaration(name_decl[0], args[0][0].lower(), ast,
                                                       binders=binders, type=type_))
            proof = True
        elif tag in ("VernacFixpoint", "VernacCoFixpoint"):
            for fix in args[1]:
                decl = declaration(fix["fname"], "recursive function" if tag == "VernacFixpoint" else "corecursive function",
                                   ast, binders=fix["binders"], body=fix["body_def"], type=fix["rtype"])
                if fix["rec_order"] is not None:
                    decl.metadata.append(source.fragment(fix["rec_order"]))
                source.declarations.append(decl)
                if fix["body_def"] is None:
                    proof = True
        elif tag in ("VernacInstance", "VernacDeclareInstance"):
            name_decl, binders, type_ = args[:3]
            body = args[3][1] if tag == "VernacInstance" and args[3] else None
            source.declarations.append(declaration(name_decl[0], "instance", ast,
                                                   binders=binders, type=type_, body=body))
            if tag == "VernacInstance" and body is None:
                proof = True
        elif tag == "VernacInductive":
            for ind, notations in args[1]:
                name_node = ind[0][1][0]
                decl = declaration(name_node, args[0][0].lower(), ast, binders=ind[1][0], type=ind[2])
                if ind[1][1]:
                    decl.binders.extend(ind[1][1])
                constructors = ind[3]
                if constructors[0] == "Constructors":
                    for attributes, (name, type_) in constructors[1]:
                        decl.children.append(declaration(name, "constructor", ast, type=type_))
                elif constructors[0] == "RecordDecl":
                    if constructors[1]:
                        decl.children.append(declaration(constructors[1], "constructor", ast))
                    for field_, attributes in constructors[2]:
                        if field_[0] == "AssumExpr":
                            decl.children.append(declaration(field_[1], "field", ast, binders=field_[2], type=field_[3]))
                        else:
                            decl.children.append(declaration(field_[1], "field", ast, binders=field_[2], body=field_[3], type=field_[4]))
                if notations:
                    decl.unsupported = True
                    decl.metadata.append("Attached notations are retained in the original declaration.")
                source.declarations.append(decl)
        else:
            # Retain other *named* commands without exposing tactic/proof bodies.
            names = []
            loc = ast.get("loc") or {}
            for offset, (identity, kind) in source.glob.definitions.items():
                if loc.get("bp", 0) <= offset < loc.get("ep", 0) and kind not in ("binder", "var", "notation"):
                    names.append((offset, identity, kind))
            if names:
                offset, identity, kind = names[0]
                name_node = {"v": ["Id", identity.split(".")[-1]], "loc": {"bp": offset, "ep": offset + len(identity.split(".")[-1].encode())}}
                decl = declaration(name_node, kind, ast, unsupported=True)
                for offset, identity, kind in names[1:]:
                    child = {"v": ["Id", identity.split(".")[-1]], "loc": {"bp": offset, "ep": offset + len(identity.split(".")[-1].encode())}}
                    decl.children.append(declaration(child, kind, ast, unsupported=True))
                source.declarations.append(decl)
        if proof:
            proof_owners = source.declarations[previous_count:]
            for owner in proof_owners:
                owner.proof_complete = False
    # A top-level fixpoint's recursive references use Rocq's lexical suffix
    # (e.g. Module.count:3), although its definition is Module.count. Associate
    # these exact qualified identities within the defining mutual block.
    # Nested local fixpoints are unsupported; do not guess their shadowing.
    recursive = [d for d in source.declarations if d.kind in ("recursive function", "corecursive function")]
    for decl in recursive:
        if any(isinstance(value(n), list) and value(n) and value(n)[0] in ("CFix", "CCoFix") for n in walk(decl.body)):
            continue
        peers = {d.identity for d in recursive if d.source_start == decl.source_start}
        stop = decl.source_start + len(decl.source.encode())
        for offset, (end, identity, kind) in list(source.glob.references.items()):
            base, separator, ordinal = identity.rpartition(":")
            if kind == "def" and separator and ordinal.isdecimal() and base in peers and decl.source_start <= offset < stop:
                source.glob.references[offset] = (end, base, kind)
    return source.declarations


class Adapter:
    def __init__(self, source, dictionary, known_symbols, resolved=None):
        self.source = source
        self.dictionary = dictionary
        self.known_symbols = known_symbols
        self.resolved = resolved or {}
        self.coverage = []
        self.encounters = {}
        self.prefix = ""
        self.synthetic_binders = 0
        self.reference_offsets = sorted(source.glob.references)

    def fallback(self, node, reason):
        text = self.source.fragment(node) or "<source unavailable>"
        self.coverage.append(reason)
        return Doc(Token("original Rocq [" + reason + "]"), [Doc(Token(text), raw=True)], block=True)

    def cjr_fallback(self, token, arguments, env, reason):
        self.coverage.append("Cangjie unavailable: " + reason)
        return Doc(Token("CJR " + token.text + " [" + reason + "]", identity=token.identity),
                   [self.term(arg, env) for arg in arguments])

    def ref(self, node, env):
        name = identifier(node)
        loc = node.get("loc") or {}
        reference = self.source.glob.references.get(loc.get("bp", -1))
        if reference and reference[2] == "var":
            if reference[1] in env:
                return Token(name, local=env[reference[1]])
        if name in env and not (reference and reference[2] != "var"):
            return Token(name, local=env[name])
        if reference and reference[2] != "var":
            identity = reference[1]
        elif loc.get("bp") in self.resolved:
            identity = self.resolved[loc["bp"]]
        elif name in self.known_symbols:
            identity = name
        else:
            identity = name
        return Token(name, identity=identity)

    def binder(self, name_node, env):
        name = identifier(name_node)
        if name == "_":
            return leaf("_")
        offset = (name_node.get("loc") or {}).get("bp")
        if offset is None:
            self.synthetic_binders += 1
            offset = f"synthetic-{self.synthetic_binders}"
        binding = f"{self.prefix}-binder-{offset}"
        env[name] = binding
        definition = self.source.glob.definitions.get(offset)
        if definition and definition[1] in ("binder", "var"):
            env[definition[0]] = binding
        return leaf(name, anchor=binding)

    def binders(self, binders, env):
        result = []
        for binder in binders:
            tag, *args = binder
            if tag == "CLocalAssum":
                names, relevance, kind, type_ = args
                type_doc = self.term(type_, env)
                label = "parameter"
                if kind[0] == "Generalized":
                    label = "typeclass " + ("maximal implicit" if kind[1][0] == "MaxImplicit" else kind[1][0].lower()) + (" !" if kind[2] else "")
                elif kind[1][0] != "Explicit":
                    label = "implicit " + kind[1][0]
                result.append(Doc(Token(label), [*(self.binder(n, env) for n in names),
                                                 Doc(Token("type"), [type_doc])]))
                if relevance is not None:
                    result.append(leaf("relevance: " + json.dumps(relevance, ensure_ascii=False)))
            elif tag == "CLocalDef":
                name, relevance, body, type_ = args
                body_doc = self.term(body, env)
                type_doc = self.term(type_, env) if type_ else None
                name_doc = self.binder(name, env)
                result.append(Doc(Token("let"), [name_doc, *([type_doc] if type_doc else []), body_doc], block=True))
            else:
                result.append(self.pattern(args[0], env))
        return result

    def pattern(self, node, env):
        expr = value(node)
        tag, *args = expr
        if tag == "CPatAtom":
            if args[0] is None:
                return leaf("_")
            qid = {**args[0], "loc": args[0].get("loc") or node.get("loc")}
            loc = qid.get("loc") or {}
            ref = self.source.glob.references.get(loc.get("bp", -1))
            token = self.ref(qid, {})
            if ref and ref[2] != "var" or token.identity in self.known_symbols:
                return Doc(token)
            # Atom patterns with unresolved constructor identity stay unlinked;
            # a lexical binding only affects occurrences in this branch.
            return self.binder(qid, env)
        if tag == "CPatCstr":
            qid, explicit, children = args
            parts = [self.pattern(p, env) for p in (explicit or []) + children]
            return Doc(self.ref(qid, {}), parts)
        if tag == "CPatAlias":
            return Doc(Token("as"), [self.pattern(args[0], env), self.binder(args[1], env)])
        if tag == "CPatOr":
            return Doc(Token("or_pattern"), [self.pattern(p, env) for p in args[0]])
        if tag == "CPatNotation":
            scope, (entry, key), substitution, extra = args
            terms, lists, binders = substitution
            children = [self.pattern(p, env) for p in terms]
            children.extend(Doc(Token("items"), [self.pattern(p, env) for p in ps]) for ps in lists)
            children.extend(self.pattern(p, env) for p, kind in binders)
            children.extend(self.pattern(p, env) for p in extra)
            return self.template("notation", key, Token(key), children, node, scope, entry)
        if tag == "CPatDelimiters":
            return Doc(Token("scope " + args[1]), [self.pattern(args[2], env)])
        if tag == "CPatPrim":
            return leaf(self.source.fragment(node))
        return self.fallback(node, tag)

    def template(self, kind, key, label, children, node, scope=None, entry=None):
        scope_name = scope[1] if scope and scope[0] == "NotationInScope" else None
        if kind == "notation":
            # .glob's notation identity records the scope selected by Rocq,
            # including scope inference absent from the concrete AST.
            encoded = "_".join("x" if part == "_" else "'" + part + "'" for part in key.split())
            loc = node.get("loc") or {}
            first = bisect.bisect_left(self.reference_offsets, loc.get("bp", 0))
            last = bisect.bisect_left(self.reference_offsets, loc.get("ep", 0))
            for offset in self.reference_offsets[first:last]:
                _, identity, ref_kind = self.source.glob.references[offset]
                if ref_kind == "not" and "::" in identity:
                    selected_scope, _, notation = identity.rsplit("::", 1)[1].partition(":")
                    if notation == encoded:
                        scope_name = selected_scope or None
                        label = Token(label.text, identity=identity)
                        break
        entry_name = entry[0] if isinstance(entry, list) and len(entry) == 1 else json.dumps(entry, ensure_ascii=False) if entry else None
        rule = self.dictionary.match(kind, key, len(children), scope_name, entry_name, label.identity)
        selector = (kind, key, len(children), scope_name, entry_name, label.identity if kind == "notation" else None)
        self.encounters.setdefault(selector, (label, children, self.source.fragment(node)))
        if rule:
            if rule["label"].startswith("CJR "):
                self.coverage.append("Cangjie unavailable: " + rule["label"])
            sort = self.source.arrow_sorts.get((node.get("loc") or {}).get("bp"), "unknown")
            if rule.get("when") == "proposition" and sort == "unknown":
                self.coverage.append("unclassified arrow at byte " + str((node.get("loc") or {}).get("bp", "?")))
            return self.dictionary.apply(rule, label, children, proposition=sort == "proposition")
        if kind == "application":
            return Doc(label, children)
        # The notation's exact grammar key remains visible, with all slots.
        self.coverage.append("unmapped notation " + key)
        return Doc(Token("notation " + json.dumps(key, ensure_ascii=False)), children, block=True)

    def term(self, node, env=None):
        env = dict(env or {})
        if node is None:
            return leaf("unspecified")
        expr = value(node)
        tag, *args = expr
        if tag == "CRef":
            token = self.ref(args[0], env)
            result = Doc(token)
            if args[1] is not None:
                return self.fallback(node, "explicit universes")
            return self.template("application", token.identity or token.text, token, [], node)
        if tag in ("CApp", "CAppExpl"):
            if tag == "CApp":
                callee, arguments = args
                callee_expr = value(callee)
                special = None
                if callee_expr[0] == "CRef" and callee_expr[2] is None:
                    token = self.ref(callee_expr[1], env)
                    from .cangjie import contextual
                    if all(explicit is None for _, explicit in arguments):
                        special = contextual(self, token, [term for term, _ in arguments], node, env)
                    if isinstance(special, Doc):
                        return special
                children = []
                for term, explicit in arguments if special is None else []:
                    child = self.term(term, env)
                    if explicit is not None:
                        child = Doc(Token("named argument " + self.source.fragment(explicit)), [child])
                    children.append(child)
                if special is not None:
                    children = special
                if callee_expr[0] != "CRef":
                    return Doc(Token("apply"), [self.term(callee, env), *children])
                if callee_expr[2] is not None:
                    return self.fallback(node, "explicit universes")
                token = self.ref(callee_expr[1], env)
            else:
                (qid, universes), arguments = args
                if universes is not None:
                    return self.fallback(node, "explicit universes")
                token = self.ref(qid, env)
                children = [self.term(term, env) for term in arguments]
            rendered = self.template("application", token.identity or token.text, token, children, node)
            return Doc(Token("explicit application"), [rendered]) if tag == "CAppExpl" else rendered
        if tag in ("CProdN", "CLambdaN"):
            binder_docs = self.binders(args[0], env)
            return Doc(Token("forall" if tag == "CProdN" else "lambda"), [*binder_docs, self.term(args[1], env)], block=True)
        if tag == "CLetIn":
            name, body, type_, rest = args
            body_doc = self.term(body, env)
            type_doc = self.term(type_, env) if type_ else None
            name_doc = self.binder(name, env)
            return Doc(Token("let"), [name_doc, *([type_doc] if type_doc else []), body_doc, self.term(rest, env)], block=True)
        if tag == "CCases":
            style, return_, cases, branches = args
            children = []
            for term, as_, in_ in cases:
                case_doc = self.term(term, env)
                if as_:
                    case_doc = Doc(Token("as"), [case_doc, self.binder(as_, env)])
                if in_:
                    case_doc = Doc(Token("in"), [case_doc, self.pattern(in_, env)])
                children.append(case_doc)
            if return_:
                children.append(Doc(Token("return type"), [self.term(return_, env)]))
            for branch in branches:
                patterns, body = value(branch)
                branch_env = dict(env)
                pattern_docs = [Doc(Token("patterns"), [self.pattern(p, branch_env) for p in group]) for group in patterns]
                children.append(Doc(Token("case"), [*pattern_docs, self.term(body, branch_env)], block=True))
            return Doc(Token("match " + style[0]), children, block=True)
        if tag == "CIf":
            condition, (as_, return_), yes, no = args
            children = [self.term(condition, env)]
            if as_:
                children.append(Doc(Token("as"), [self.binder(as_, env)]))
            if return_:
                children.append(Doc(Token("return type"), [self.term(return_, env)]))
            children.extend([Doc(Token("then"), [self.term(yes, env)], block=True),
                             Doc(Token("else"), [self.term(no, env)], block=True)])
            return Doc(Token("if"), children, block=True)
        if tag == "CLetTuple":
            names, (as_, return_), term, body = args
            term_doc = self.term(term, env)
            binders = [self.binder(n, env) for n in names]
            if as_:
                binders.append(self.binder(as_, env))
            if return_:
                binders.append(Doc(Token("return type"), [self.term(return_, env)]))
            return Doc(Token("let tuple"), [*binders, term_doc, self.term(body, env)], block=True)
        if tag == "CNotation":
            scope, (entry, key), substitution = args
            terms, lists, patterns, binder_lists = substitution
            # Notation binders are introduced before their term bodies. This
            # preserves existential / WP postcondition scopes from the AST.
            outer_env = dict(env)
            binder_docs = [self.pattern(p, env) for p, kind in patterns]
            binder_docs.extend(Doc(Token("binders"), self.binders(bs, env), block=True) for bs in binder_lists)
            if key.startswith("WP ") and "{{ _ , _ } }" in key and len(terms) >= 3:
                # WP's postcondition binder is serialized as a term slot.
                prefix_terms, binder_term, post = terms[:-2], terms[-2], terms[-1]
                if value(binder_term)[0] == "CRef":
                    post_binder = self.binder(value(binder_term)[1], env)
                elif value(binder_term)[0] == "CHole":
                    post_binder = leaf("_")
                else:
                    return self.fallback(node, "unsupported WP binder")
                children = [*(self.term(t, outer_env) for t in prefix_terms),
                            Doc(Token("post binder"), [post_binder]),
                            Doc(Token("postcondition"), [self.term(post, env)], block=True)]
            else:
                children = [self.term(t, outer_env if key.startswith("[∗") and i == 0 else env)
                            for i, t in enumerate(terms)]
            children.extend(Doc(Token("items"), [self.term(t, env) for t in ts]) for ts in lists)
            children.extend(binder_docs)
            return self.template("notation", key, Token(key), children, node, scope, entry)
        if tag == "CDelimiters":
            depth, scope, term = args
            label = "in_scope " if depth[0] == "DelimUnboundedScope" else "in_temporary_scope "
            return Doc(Token(label + scope), [self.term(term, env)])
        if tag == "CPrim":
            return leaf(self.source.fragment(node))
        if tag == "CSort":
            return leaf(self.source.fragment(node))
        if tag == "CHole":
            return leaf("_ (inferred)")
        if tag == "CCast":
            term, kind, type_ = args
            return Doc(Token("cast " + (kind[0] if kind else "type")), [self.term(term, env), self.term(type_, env)])
        if tag == "CGeneralization":
            return Doc(Token("generalize " + args[0][0]), [self.term(args[1], env)])
        if tag == "CRecord":
            return Doc(Token("record"), [Doc(self.ref(q, env), [self.term(t, env)]) for q, t in args[0]], block=True)
        if tag == "CProj":
            explicit, (qid, universes), arguments, term = args
            if universes is not None:
                return self.fallback(node, "projection universes")
            return Doc(Token("explicit projection" if explicit else "projection"), [Doc(self.ref(qid, env)),
                       *[self.term(t, env) if x is None else Doc(Token("named " + self.source.fragment(x)), [self.term(t, env)])
                         for t, x in arguments], self.term(term, env)])
        return self.fallback(node, tag)

    def declaration(self, declaration):
        self.prefix = anchor(declaration.identity)
        env = {}
        children = []
        if declaration.context:
            children.append(Doc(Token("context"), self.binders(declaration.context, env), block=True))
        children.extend(self.binders(declaration.binders, env))
        if declaration.type:
            children.append(Doc(Token("type" if declaration.body else "statement"), [self.term(declaration.type, env)], block=True))
        if declaration.body:
            children.append(Doc(Token("body"), [self.term(declaration.body, env)], block=True))
        for child in declaration.children:
            token = Token(child.name, anchor=anchor(child.identity))
            child_env = dict(env)
            parts = self.binders(child.binders, child_env)
            if child.type:
                parts.append(self.term(child.type, child_env))
            if child.body:
                parts.append(self.term(child.body, child_env))
            children.append(Doc(token, parts))
        for metadata in declaration.metadata:
            children.append(Doc(Token("declaration metadata"), [Doc(Token(metadata), raw=True)], block=True))
        if declaration.unsupported:
            self.coverage.append("unsupported declaration " + declaration.kind)
            children.append(Doc(Token("original Rocq"), [Doc(Token(declaration.source), raw=True)], block=True))
        return Doc(Token(declaration.kind + " " + declaration.name), children, block=True)
