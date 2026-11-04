"""A parsed-source display adapter, separate from legacy explanation inputs."""
from dataclasses import replace
from pathlib import Path

from .ast import Adapter, value
from .layout import Doc, Token, leaf
from .program_syntax import ProgramSyntax, LEMMAS, custom_rule, type_alias, phrase


class DisplayAdapter(Adapter):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.program = ProgramSyntax(self, self.application, self.string, self.read_list)
        self.program_serial = 0
        self.details = []

    def application(self, node):
        expr = value(node)
        if not isinstance(expr, list) or not expr:
            return None, []
        if expr[0] == 'CRef' and expr[2] is None:
            token = self.ref(expr[1], {})
            return token.identity, []
        if expr[0] == 'CApp' and value(expr[1])[0] == 'CRef' and value(expr[1])[2] is None:
            if all(explicit is None for _, explicit in expr[2]):
                token = self.ref(value(expr[1])[1], {})
                return token.identity, [a for a, _ in expr[2]]
        return None, []

    def string(self, node):
        expr = value(node)
        return expr[1][1] if isinstance(expr, list) and expr and expr[0] == 'CPrim' and expr[1][0] == 'String' else None

    def read_list(self, node):
        expr = value(node)
        if isinstance(expr, list) and expr and expr[0] == 'CNotation':
            key = expr[2][1]
            terms, lists, patterns, binders = expr[3]
            encoded = '_'.join('x' if p == '_' else "'" + p + "'" for p in key.split())
            loc = node.get('loc') or {}
            resolved = any(kind == 'not' and identity ==
                           'Coq.Lists.List.ListNotations.::list_scope:' + encoded
                           for offset, (_, identity, kind) in self.source.glob.references.items()
                           if loc.get('bp', 0) <= offset < loc.get('ep', 0))
            if resolved and not patterns and not binders:
                if key == '[ ]' and not terms and not lists:
                    return []
                if key == '[ _ ]' and len(terms) == 1 and not lists:
                    return terms
                if key == '[ _ ; _ ; .. ; _ ]' and len(terms) == 1 and len(lists) == 1:
                    return [*terms, *lists[0]]
        return None

    def program_binding(self, name, env):
        self.program_serial += 1
        taken = {*env, *(t.text for t in self.program.bindings.values())}
        base, suffix = name, 1
        while name in taken:
            suffix += 1
            name = base + str(suffix)
        return Token(name, anchor=f'{self.prefix}-program-{self.program_serial}')

    def coverage_notice(self, reason):
        self.coverage.append(reason)

    def postcondition(self, node, env, state=False):
        expr = value(node)
        if isinstance(expr, list) and expr[0] == 'CNotation' and expr[2][1] in ('λ _ .. _ , _', 'fun _ .. _ => _'):
            terms, lists, patterns, binders = expr[3]
            if len(terms) == 1 and not lists and not patterns and binders:
                expr = ['CLambdaN', [b for group in binders for b in group], terms[0]]
        if not isinstance(expr, list) or expr[0] != 'CLambdaN':
            return self.term(node, env)
        nested, names = dict(env), []
        for binder in expr[1]:
            if binder[0] != 'CLocalAssum':
                return self.term(node, env)
            for name in binder[1]:
                doc = self.binder(name, nested)
                names.append(doc)
        if len(names) != (2 if state else 1):
            return self.term(node, env)
        body = self.term(expr[2], nested)
        result = names[0] if names[0].label.text != '_' else leaf('result')
        if state:
            final = names[1]
            used = final.label.anchor and any(t.local == final.label.anchor for _, ts in body.lines() for t in ts)
            if used:
                return phrase('on return {0}, in state {1}:\n  {2}', [result, final, body])
        return phrase('on return {0}:\n  {1}', [result, body])

    def term(self, node, env=None):
        env = dict(env or {})
        key, args = self.application(node)
        if key and not custom_rule(self.dictionary, key, len(args)):
            alias = type_alias(key, args, self.application)
            if alias is not None:
                return alias
            rendered = self.program.render(key, args, env)
            if rendered is not None:
                return rendered
            if key == 'iris.program_logic.adequacy.adequate' and len(args) == 4:
                return Doc(Token('adequate', identity=key), [*[self.term(a, env) for a in args[:3]], self.postcondition(args[3], env, state=True)], plain_indent=2)
        rendered = super().term(node, env)
        expr = value(node)
        if isinstance(expr, list) and expr and expr[0] == 'CNotation' and expr[2][1].startswith('WP '):
            # The legacy adapter has already resolved the notation's result binder.
            # Do not reinterpret an explicitly selected custom notation template.
            default = self.dictionary.path.resolve() == Path(__file__).with_name('renderings.json').resolve()
            binder = next((c for c in rendered.children if c.label.text == 'post binder'), None)
            post = next((c for c in rendered.children if c.label.text == 'postcondition'), None)
            if default and rendered.template is None and binder and post:
                name = binder.children[0]
                if name.label.text == '_':
                    name = leaf('result')
                rendered = replace(rendered, children=[c for c in rendered.children if c is not binder and c is not post] +
                    [phrase('on return {0}:\n  {1}', [name, post.children[0]])])
        return rendered

    def declaration(self, declaration):
        self.program.bindings = {}
        self.program_serial = 0
        self.details = []
        doc = super().declaration(declaration)
        if declaration.kind in LEMMAS:
            doc = replace(doc, children=[part for child in doc.children for part in
                          (child.children if child.label.text in ('type', 'statement') else [child])])
        return replace(doc, plain_indent=2)
