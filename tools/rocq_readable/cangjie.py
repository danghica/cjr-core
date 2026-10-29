"""Contextual CJR identifiers/binders; surface spelling lives in the dictionary."""
import re

from .ast import value
from .layout import Doc, Token, leaf


KEYWORDS = set("this super init main func let var type in is as where match case class struct spawn true false if else while for do return break continue".split())


def string_name(node):
    expr = value(node)
    if isinstance(expr, list) and expr and expr[0] == "CPrim" and expr[1][0] == "String":
        name = expr[1][1]
        if name != "_" and re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", name):
            return "self" if name == "this" else name + "_" if name in KEYWORDS else name
    return None


def contextual(adapter, token, arguments, node, env):
    """Return special argument documents, or None for ordinary adaptation."""
    key = token.identity
    if not key or not key.startswith("cjr.lang."):
        return None
    rule = adapter.dictionary.match("application", key, len(arguments))
    if not rule or "template" not in rule:
        return None
    name = key.rsplit(".", 1)[1]

    def optional(term):
        expr = value(term)
        if expr[0] == "CRef" and adapter.ref(expr[1], env).identity == "Coq.Init.Datatypes.None":
            return "_", term
        if expr[0] == "CApp" and value(expr[1])[0] == "CRef" and adapter.ref(value(expr[1])[1], env).identity == "Coq.Init.Datatypes.Some" and len(expr[2]) == 1:
            inner = expr[2][0][0]
            return string_name(inner), inner
        return None, term

    if name in ("Var", "Assign", "VarBind", "Let", "Rec", "RecV"):
        if not arguments:
            return None
        binder_slot = 1 if name in ("Rec", "RecV") else 0
        term = arguments[binder_slot]
        spelling, name_node = optional(term) if name in ("Let", "Rec", "RecV") else (string_name(term), term)
        if spelling is None:
            return adapter.cjr_fallback(token, arguments, env, "symbolic identifier or binder")
        children = []
        body_env = dict(env)
        binding = None
        if name in ("Let", "VarBind", "Rec", "RecV") and spelling != "_":
            offset = (name_node.get("loc") or {}).get("bp", (node.get("loc") or {}).get("bp"))
            binding = f"{adapter.prefix}-cangjie-binder-{offset}"
            body_env["#cjr:" + spelling] = binding
        for i, arg in enumerate(arguments):
            if name in ("Rec", "RecV") and i == 0:
                recursive, _ = optional(arg)
                if recursive != "_":
                    return adapter.cjr_fallback(token, arguments, env, "recursive or symbolic closure")
                children.append(leaf(""))
            elif i == binder_slot:
                children.append(leaf(spelling, anchor=binding) if binding else leaf(spelling, local=env.get("#cjr:" + spelling)))
            else:
                children.append(adapter.term(arg, body_env if i == len(arguments) - 1 and binding else env))
        return children
    if name == "LitBool" and len(arguments) == 1:
        expr = value(arguments[0])
        if expr[0] == "CRef":
            boolean = adapter.ref(expr[1], env)
            if boolean.identity in ("Coq.Init.Datatypes.true", "Coq.Init.Datatypes.false"):
                return [Doc(Token(boolean.identity.rsplit(".", 1)[1], identity=boolean.identity))]
    if name == "LitFloat" and len(arguments) == 1 and value(arguments[0])[0] != "CPrim":
        return adapter.cjr_fallback(token, arguments, env, "symbolic float literal")
    return None
