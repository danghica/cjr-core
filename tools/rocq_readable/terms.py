"""Deterministic plain-language skin over resolved Rocq terms, never proof text."""
from __future__ import annotations

import json

from .layout import Doc, Token, anchor, leaf
from .program_syntax import ProgramSyntax, LEMMAS, custom_rule, type_alias

BI = 'iris.bi.interface.'
BINARY = {
    BI + 'bi_wand': 'resource promise', BI + 'bi_sep': 'separately',
    BI + 'bi_and': 'both', BI + 'bi_or': 'either', BI + 'bi_impl': 'if … then',
    BI + 'bi_entails': 'entails',
    'Coq.Init.Logic.and': 'both', 'Coq.Init.Logic.or': 'either',
    'Coq.Init.Logic.iff': 'if and only if',
}
UNARY = {
    BI + 'bi_pure': 'pure', BI + 'bi_persistently': 'persistent', BI + 'bi_later': 'later',
    'iris.bi.derived_connectives.bi_affinely': 'affine',
    'iris.bi.derived_connectives.bi_absorbingly': 'absorbing',
    'iris.bi.derived_connectives.bi_intuitionistically': 'intuitionistic',
    'iris.bi.derived_connectives.bi_except_0': 'except zero',
    'iris.bi.updates.bupd': 'update',
    'Coq.Init.Logic.not': 'not',
}
INFIX = {
    'Coq.Init.Logic.eq': '=',
    'Coq.Init.Nat.add': '+', 'Coq.Init.Nat.sub': '-', 'Coq.Init.Nat.mul': '*',
    'Coq.Arith.PeanoNat.Nat.add': '+',
    'Coq.ZArith.BinInt.Z.add': '+', 'Coq.ZArith.BinInt.Z.sub': '-',
    'Coq.ZArith.BinInt.Z.mul': '*', 'Coq.ZArith.BinInt.Z.le': '≤',
    'Coq.ZArith.BinInt.Z.lt': '<',
}
WP = {'iris.bi.weakestpre.wp', 'iris.bi.weakestpre.twp'}
QUANTIFIERS = {BI + 'bi_forall': 'every', BI + 'bi_exist': 'exists', 'Coq.Init.Logic.ex': 'exists'}


def identity(node):
    return node.get('identity') if node.get('tag') in ('ref', 'projection') else None


def application(node):
    if node.get('tag') == 'app':
        return identity(node['head']), [a['term'] for a in node['arguments'] if not a['implicit']]
    return identity(node), []


def number(node):
    key, args = application(node)
    if not args and key in ('Coq.Init.Datatypes.O', 'Coq.Numbers.BinNums.Z0'):
        return 0
    if not args and key == 'Coq.Numbers.BinNums.xH':
        return 1
    if len(args) == 1:
        value = number(args[0])
        if value is not None:
            return {'Coq.Init.Datatypes.S': lambda: value + 1,
                    'Coq.Numbers.BinNums.xO': lambda: 2 * value,
                    'Coq.Numbers.BinNums.xI': lambda: 2 * value + 1,
                    'Coq.Numbers.BinNums.Zpos': lambda: value,
                    'Coq.Numbers.BinNums.Zneg': lambda: -value}.get(key, lambda: None)()
    return None


def string_literal(node):
    chars = []
    while True:
        key, args = application(node)
        if key == 'Coq.Strings.String.EmptyString' and not args:
            return ''.join(chars)
        if key != 'Coq.Strings.String.String' or len(args) != 2:
            return None
        char, bits = application(args[0])
        if char != 'Coq.Strings.Ascii.Ascii' or len(bits) != 8:
            return None
        value = 0
        for i, bit in enumerate(bits):
            identity_, operands = application(bit)
            if operands or identity_ not in ('Coq.Init.Datatypes.true', 'Coq.Init.Datatypes.false'):
                return None
            value += int(identity_.endswith('.true')) << i
        chars.append(chr(value))
        node = args[1]


def block(label, children, **token):
    return Doc(Token(label, **token), children, block=True, plain_indent=2)


def phrase(text, children):
    return Doc(Token(''), children, template=text, template_indent=2, plain_indent=2)


class Renderer:
    def __init__(self, declaration, dictionary):
        self.declaration = declaration
        self.dictionary = dictionary
        self.prefix = anchor(declaration.identity) + '-elaborated-'
        self.serial = 0
        self.hidden = []
        self.unsupported = []
        self.program = ProgramSyntax(self, application, string_literal)

    def binding(self, name, env):
        self.serial += 1
        display = name if name != '_' else 'value'
        taken = {t.text for t in env}
        base, suffix = display, 1
        while display in taken:
            suffix += 1
            display = base + str(suffix)
        return Token(display, anchor=self.prefix + str(self.serial))

    def program_binding(self, name, env):
        return self.binding(name, [*env, *self.program.bindings.values()])

    def coverage_notice(self, reason):
        self.unsupported.append(reason)

    def use(self, token):
        return Doc(Token(token.text, local=token.anchor))

    def binder_doc(self, token, type_, env):
        return phrase('{0}: {1}', [Doc(token), self.term(type_, env)])

    def term(self, node, env):
        tag = node['tag']
        integer = number(node)
        if integer is not None:
            return leaf(str(integer))
        literal = string_literal(node)
        if literal is not None:
            return leaf(json.dumps(literal, ensure_ascii=False))
        if tag == 'ref':
            rule = custom_rule(self.dictionary, node['identity'], 0)
            if rule and not rule.get('when'):
                return self.dictionary.apply(rule, Token(node['identity'].split('.')[-1], identity=node['identity']), [])
            if not rule:
                alias = type_alias(node['identity'], [], application)
                if alias is not None:
                    return alias
                program = self.program.render(node['identity'], [], env)
                if program is not None:
                    return program
            return leaf(node['identity'].split('.')[-1], identity=node['identity'])
        if tag == 'var':
            found = next((t for t in reversed(env) if t.text == node['name']), None)
            return self.use(found) if found else leaf(node['name'])
        if tag == 'rel':
            i = node['index']
            if i < 1 or i > len(env):
                self.unsupported.append('unbound elaborated binder')
                return leaf('unbound binder ' + str(i), css='unsupported')
            return self.use(env[-i])
        if tag in ('sort', 'literal'):
            return leaf(node['text'])
        if tag in ('product', 'lambda'):
            token = self.binding(node['name'], env)
            type_ = self.term(node['type'], env)
            body = self.term(node['body'], [*env, token])
            if tag == 'product' and node['name'] == '_' and node.get('proposition') and node.get('premise_proposition'):
                return phrase('if:\n  {0}\nthen:\n  {1}', [type_, body])
            label = 'function type' if tag == 'product' and node['name'] == '_' else 'every' if tag == 'product' else 'function'
            return phrase(label + ' {0}: {1}\n  {2}', [Doc(token), type_, body])
        if tag == 'let':
            token = self.binding(node['name'], env)
            return phrase('let {0}: {1} = {2}\nin:\n  {3}', [Doc(token), self.term(node['type'], env),
                          self.term(node['value'], env), self.term(node['body'], [*env, token])])
        if tag == 'cast':
            return phrase('{0}: {1}', [self.term(node['value'], env), self.term(node['type'], env)])
        if tag == 'projection':
            return Doc(Token(node['identity'].split('.')[-1], identity=node['identity']), [self.term(node['value'], env)])
        if tag == 'app':
            return self.app(node, env)
        if tag == 'match':
            branches = [block('when ' + b['constructor'].split('.')[-1], [self.term(b['body'], env)], identity=b['constructor'])
                        for b in node['branches']]
            return block('match', [self.term(node['scrutinee'], env), block('return', [self.term(node['return'], env)]), *branches])
        if tag in ('fix', 'cofix'):
            definitions = node['definitions']
            tokens = [self.binding(d['name'], env) for d in definitions]
            inner = [*env, *tokens]
            bodies = [block('definition', [Doc(token), block('type', [self.term(d['type'], env)]),
                      block('body', [self.term(d['body'], inner)])]) for token, d in zip(tokens, definitions)]
            selected = definitions[node['selected']]['name']
            decreasing = ', '.join(str(i + 1) for i in node['decreasing'])
            return block(('recursive' if tag == 'fix' else 'corecursive') + ' function ' + selected,
                         ([leaf('decreasing arguments: ' + decreasing)] if decreasing else []) + bodies)
        if tag == 'array':
            return block('array', [block('type', [self.term(node['type'], env)]),
                         block('values', [self.term(t, env) for t in node['values']]),
                         block('default', [self.term(node['default'], env)])])
        self.unsupported.append('elaborated ' + tag)
        return leaf('unresolved: ' + node.get('text', tag) + ' (see elaboration details)', css='unsupported')

    def app(self, node, env):
        key, args = application(node)
        # Rules operate on explicit arguments; the complete application, including
        # the projection's instance and every implicit slot, remains in details.
        if key and not custom_rule(self.dictionary, key, len(args)):
            alias = type_alias(key, args, application)
            if alias is not None:
                return alias
            program = self.program.render(key, args, env)
            if program is not None:
                return program
        if key:
            rule = self.dictionary.match('application', key, len(args))
            if rule and not rule.get('when'):
                return self.dictionary.apply(rule, Token(key.split('.')[-1], identity=key), [self.term(a, env) for a in args])
        if key == 'iris.program_logic.adequacy.adequate' and len(args) == 4:
            return Doc(Token('adequate', identity=key), [*[self.term(a, env) for a in args[:3]],
                       self.postcondition(args[3], env, state=True)], plain_indent=2)
        if key in QUANTIFIERS and args and args[-1]['tag'] == 'lambda':
            predicate = args[-1]
            token = self.binding(predicate['name'], env)
            return phrase(QUANTIFIERS[key] + ' {0}: {1}\n  {2}', [Doc(token), self.term(predicate['type'], env), self.term(predicate['body'], [*env, token])])
        if key in BINARY and len(args) == 2:
            return block(BINARY[key], [self.term(a, env) for a in args], identity=key)
        if key in UNARY and len(args) == 1:
            return block(UNARY[key], [self.term(args[0], env)], identity=key)
        if key in INFIX and len(args) == 2:
            return phrase('{0} ' + INFIX[key] + ' {1}', [self.term(a, env) for a in args])
        if key == BI + 'bi_emp_valid' and len(args) == 1:
            return block('valid from empty resources', [self.contract(args[0], env)], identity=key)
        if key == 'iris.bi.updates.fupd' and len(args) == 3:
            return block('update', [block('from mask', [self.term(args[0], env)]), block('to mask', [self.term(args[1], env)]), self.term(args[2], env)], identity=key)
        if key in WP and len(args) == 4:
            return self.wp(key, args, [], env)
        ownership = {'cjr.primitive_laws.raw_mapsto': ('owns_raw', 2),
                     'cjr.primitive_laws.stack_mapsto': ('owns_stack', 2),
                     'cjr.primitive_laws.obj_mapsto': ('owns_object_field', 3),
                     'cjr.primitive_laws.block_mapsto': ('owns_block', 2)}
        if key in ownership and len(args) == ownership[key][1]:
            return Doc(Token(ownership[key][0], identity=key), [self.term(a, env) for a in args])
        head = self.term(node['head'], env)
        if not args:
            return head
        return (Doc(head.label, [self.term(a, env) for a in args]) if node["head"]["tag"] in ("ref", "projection", "rel", "var")
                else block("apply", [head, *[self.term(a, env) for a in args]]))

    def contract(self, node, env):
        """Collect only the outer wand chain immediately ending in a WP."""
        requirements = []
        current = node
        while True:
            key, args = application(current)
            if key != BI + 'bi_wand' or len(args) != 2:
                break
            requirements.append(args[0])
            current = args[1]
        key, args = application(current)
        if key in WP and len(args) == 4:
            return self.wp(key, args, requirements, env)
        return self.term(node, env)

    def postcondition(self, node, env, state=False):
        if node['tag'] != 'lambda':
            return self.term(node, env)
        token = self.binding(node['name'] if node['name'] != '_' else 'result', env)
        self.hidden.append(phrase('{0}: {1}', [self.use(token), self.term(node['type'], env)]))
        nested = [*env, token]
        body = node['body']
        if state and body['tag'] == 'lambda':
            final = self.binding(body['name'] if body['name'] != '_' else 'state', nested)
            from .program_syntax import uses_rel
            used = uses_rel(body['body'])
            type_ = self.term(body['type'], nested)
            self.hidden.append(phrase('{0}: {1}', [self.use(final) if used else Doc(final), type_]))
            guarantee = self.term(body['body'], [*nested, final])
            if used:
                return phrase('on return {0}, in state {1}:\n  {2}', [Doc(token), Doc(final), guarantee])
            return phrase('on return {0}:\n  {1}', [Doc(token), guarantee])
        return phrase('on return {0}:\n  {1}', [Doc(token), self.term(body, nested)])

    def wp(self, key, args, requirements, env):
        stuckness, mask, expression, post = args
        parts = []
        if requirements:
            parts.append(block('requires (resource promises)', [self.term(r, env) for r in requirements]))
        if identity(stuckness) == 'iris.bi.weakestpre.NotStuck':
            parts.append(leaf('safety: cannot get stuck', identity=identity(stuckness)))
        else:
            parts.append(block('stuckness', [self.term(stuckness, env)]))
        # Match the standard coPset Top instance, never an arbitrary function
        # or typeclass instance that merely prints as "top".
        top = (mask.get('tag') == 'app' and identity(mask['head']) == 'stdpp.base.top'
               and len(mask['arguments']) == 2
               and identity(mask['arguments'][-1]['term']) == 'stdpp.coPset.coPset_top')
        if top:
            parts.append(leaf('invariant access: unrestricted', identity='stdpp.base.top'))
        else:
            parts.append(block('mask', [self.term(mask, env)]))
        parts.extend([block('execute', [self.term(expression, env)]), block('ensures', [self.postcondition(post, env)])])
        return block('total correctness' if key.endswith('.twp') else 'partial correctness', parts, identity=key)

    def document(self, record):
        data = record['term']
        context, env = [], []
        for c in data['context']:
            token = self.binding(c['name'], env)
            doc = self.binder_doc(token, c['type'], env)
            if c['value'] is not None:
                doc = phrase('{0} = {1}', [doc, self.term(c['value'], env)])
            (self.hidden if c['class'] else context).append(doc)
            env.append(token)
        body_env = list(env)
        parameters, ty, body = [], data['type'], data['body']
        while ty['tag'] == 'product' and ty['name'] != '_':
            token = self.binding(ty['name'], env)
            doc = self.binder_doc(token, ty['type'], env)
            (self.hidden if ty.get('implicit') or ty.get('class') else parameters).append(doc)
            env.append(token)
            ty = ty['body']
            if body and body['tag'] == 'lambda':
                body = body['body']
                body_env.append(token)
        parts = []
        if context:
            parts.append(block('context', context))
        if parameters:
            parts.append(block('parameters', parameters))
        statement = self.contract(ty, env)
        parts.append(statement if self.declaration.kind in LEMMAS else block('type', [statement]))
        if body is not None:
            parts.append(block('definition', [self.term(body, body_env)]))
        for child in record.get('children', []):
            parts.append(block(child['identity'].split('.')[-1], [self.term(child['term']['type'], env)], identity=child['identity']))
        from .ownership import skin
        return skin(block(self.declaration.kind + ' ' + self.declaration.name, parts), self.hidden)
