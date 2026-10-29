"""Conservative, isolated sort checks in the source's Rocq environment."""
from .ast import identifier, value
from .backend import BackendError


def classify_arrows(backend, source):
    def binders(items, wrappers, visit):
        wrappers = list(wrappers)
        for item in items:
            tag, *args = value(item)
            if tag != "CLocalAssum":
                # Pattern/inferred binders need elaboration we do not have.
                return None
            names, _, _, type_ = args
            visit(type_, wrappers)
            text = source.fragment(type_)
            if not text:
                return None
            wrappers.append("forall (" + " ".join(identifier(n) for n in names) + " : " + text + "), ")
        return wrappers

    def declaration(decl):
        prefix = source.text.encode()[:decl.source_start].decode()
        lines = prefix.split("\n")
        position = {"line": len(lines) - 1, "character": len(lines[-1].encode("utf-16-le")) // 2}

        def check(term):
            try:
                backend.request("petanque/run_at_point", {
                    "textDocument": {"uri": source.path.as_uri(), "version": 1},
                    "position": position, "command": "Check (" + term + ")."})
                return True
            except BackendError:
                return False

        def visit(node, wrappers):
            expr = value(node)
            if isinstance(node, dict) and isinstance(expr, list) and expr:
                tag, *args = expr
                if tag == "CNotation" and args[1][1] in ("_ -> _", "_ → _"):
                    loc = node.get("loc", {})
                    offset = loc.get("bp")
                    if offset is not None and offset not in source.arrow_sorts:
                        text = source.fragment(node)
                        if wrappers is not None and text:
                            context = "".join(wrappers)
                            if check(context + "((" + text + ") : Prop)"):
                                source.arrow_sorts[offset] = "proposition"
                            elif check(context + "(" + text + ")"):
                                source.arrow_sorts[offset] = "type"
                            else:
                                source.arrow_sorts[offset] = "unknown"
                        else:
                            source.arrow_sorts[offset] = "unknown"
                if tag in ("CProdN", "CLambdaN"):
                    nested = binders(args[0], wrappers, visit) if wrappers is not None else None
                    visit(args[1], nested)
                    return
                if tag == "CLetIn":
                    name, body, type_, rest = args
                    visit(body, wrappers)
                    visit(type_, wrappers)
                    nested = None if wrappers is None else [*wrappers, "let " + identifier(name) + " := (" + source.fragment(body) + ") in "]
                    visit(rest, nested)
                    return
                if tag == "CNotation" and args[1][1] in ("∀ _ .. _ , _", "forall _ .. _ , _") and not args[2][2]:
                    terms, lists, _, binder_lists = args[2]
                    nested = wrappers
                    for items in binder_lists:
                        nested = binders(items, nested, visit) if nested is not None else None
                    visit(terms, nested)
                    visit(lists, nested)
                    return
                # Notation binders cannot safely be reconstructed as ordinary
                # Gallina binders. Unknown is preferable to a guessed sort.
                if tag == "CNotation" and (args[2][2] or args[2][3]):
                    wrappers = None
            if isinstance(node, dict):
                for key, child in node.items():
                    if key != "loc":
                        visit(child, wrappers)
            elif isinstance(node, list):
                for child in node:
                    visit(child, wrappers)

        wrappers = binders(decl.binders, [], visit)
        visit(decl.type, wrappers)
        visit(decl.body, wrappers)
        for child in decl.children:
            declaration(child)

    for decl in source.declarations:
        declaration(decl)
