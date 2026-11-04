"""Contextual CJR pseudocode shared by native and parsed display renderers.

No source edits, evaluation, layout inference, or explanation-input changes.
"""
from contextlib import contextmanager
from dataclasses import replace
from pathlib import Path
import re

from .layout import Doc, Token, leaf
from .dictionary import selector

CJR = 'cjr.lang.'
LEMMAS = {'lemma', 'theorem', 'corollary', 'proposition', 'fact', 'remark'}
ALIASES = {CJR + n: label for names, label in [
    (('val', 'val_cjr'), 'CJR value'), (('state', 'state_cjr'), 'CJR state')]
    for n in names}
LANGUAGE = 'iris.program_logic.language.'
KEYWORDS = {'let', 'var', 'function', 'recursive', 'store', 'at', 'in', 'if', 'else', 'while'}
OPERATORS = {'PlusOp': '+', 'MinusOp': '-', 'MulOp': '*', 'DivOp': '/', 'RemOp': '%',
             'LeOp': '≤', 'EqOp': '=', 'AndOp': 'and', 'BitXorOp': 'xor', 'BitAndOp': 'bit_and'}


def phrase(template, children, atomic=False):
    return Doc(Token(''), children, template=template, template_indent=2, plain_indent=2, atomic=atomic)


def call(label, children):
    return Doc(Token(label), children, plain_indent=2)


def sequence(*children):
    return phrase('\n'.join('{' + str(i) + '}' for i in range(len(children))), list(children))


def custom_rule(dictionary, key, arity):
    rule = dictionary.match('application', key, arity)
    default = Path(__file__).with_name('renderings.json').resolve()
    return rule if rule and (dictionary.path.resolve() != default or
                            selector(rule) in getattr(dictionary, 'display_overrides', set())) else None


def type_alias(key, args, app):
    if not args and key in ALIASES:
        return leaf(ALIASES[key], identity=key)
    if key in (LANGUAGE + 'val', LANGUAGE + 'state') and len(args) == 1 and app(args[0]) == (CJR + 'cjr_lang', []):
        return leaf('CJR value' if key.endswith('.val') else 'CJR state', identity=key)
    return None


def display_name(name):
    if re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', name) and name not in KEYWORDS:
        return name
    return '`' + name.replace('\\', '\\\\').replace('`', '\\`').replace('\n', '\\n').replace('\r', '\\r') + '`'


class ProgramSyntax:
    def __init__(self, host, app, string, read_list=None):
        self.host, self.app, self.string = host, app, string
        self.read_list = read_list
        self.bindings = {}

    @contextmanager
    def scope(self, additions):
        previous = self.bindings
        self.bindings = {**previous, **additions}
        try:
            yield
        finally:
            self.bindings = previous

    def optional(self, node):
        key, args = self.app(node)
        if key == 'Coq.Init.Datatypes.None' and not args:
            return True, None
        if key == 'Coq.Init.Datatypes.Some' and len(args) == 1:
            name = self.string(args[0])
            return name is not None, name
        return False, None

    def listing(self, node):
        if self.read_list:
            result = self.read_list(node)
            if result is not None:
                return result
        result = []
        while True:
            key, args = self.app(node)
            if key == 'Coq.Init.Datatypes.nil' and not args:
                return result
            if key != 'Coq.Init.Datatypes.cons' or len(args) != 2:
                return None
            result.append(args[0])
            node = args[1]

    def fresh(self, name, env):
        return self.host.program_binding(display_name(name), env)

    def variable(self, name):
        token = self.bindings.get(name)
        return Doc(Token(token.text, local=token.anchor)) if token else leaf(display_name(name))

    def unsupported(self, key, args, env, reason):
        self.host.coverage_notice('CJR ' + key.rsplit('.', 1)[-1] + ': ' + reason)
        return Doc(Token('CJR ' + key.rsplit('.', 1)[-1] + ' [' + reason + ']', identity=key),
                   [self.host.term(a, env) for a in args], plain_indent=2)

    def function(self, key, args, env, binding=None, mutable=False):
        self_ok, self_name = self.optional(args[0])
        arg_ok, arg_name = self.optional(args[1])
        if not self_ok or not arg_ok:
            return self.unsupported(key, args, env, 'symbolic function binder')
        additions = {}
        self_doc = None
        if self_name is not None:
            token = self.fresh(self_name, env)
            additions[self_name] = token
            self_doc = Doc(token)
        with self.scope(additions):
            arg_token = self.fresh(arg_name, env) if arg_name is not None else None
            if arg_token and arg_name != self_name:
                # CJR substitutes the recursive name before the argument; if
                # both names coincide, references denote the recursive closure.
                additions[arg_name] = arg_token
            arg_doc = Doc(arg_token) if arg_token else leaf('_')
            with self.scope(additions):
                body = self.host.term(args[2], env)
        children, prefix = [], ''
        if binding is not None:
            children.append(Doc(binding))
            prefix = ('var' if mutable else 'let') + ' {0} = '
        offset = len(children)
        if self_doc is not None:
            prefix += 'recursive function {' + str(offset) + '}'
            children.append(self_doc)
        else:
            prefix += 'function'
        offset = len(children)
        children.extend([arg_doc, body])
        doc = phrase(prefix + '({' + str(offset) + '}):\n  {' + str(offset + 1) + '}', children)
        return replace(doc, label=replace(doc.label, identity=key))

    def initializer_function(self, node):
        key, args = self.app(node)
        while key in (CJR + 'Val', CJR + 'LitV') and len(args) == 1:
            node = args[0]
            key, args = self.app(node)
        if key in (CJR + 'Rec', CJR + 'RecV') and len(args) == 3 and not custom_rule(self.host.dictionary, key, 3):
            return key, args
        return None

    def render(self, key, args, env):
        doc = self._render(key, args, env)
        # Transparent wrappers must not steal a helper's link or a variable's
        # local destination. Visible operations still link to their constructors.
        if doc is not None and key not in (CJR + n for n in ('Var', 'Val', 'LitV', 'LitInt', 'LitBool')):
            doc = replace(doc, label=replace(doc.label, identity=key))
        return doc

    def _render(self, key, args, env):
        if not key or not key.startswith(CJR):
            return None
        name = key[len(CJR):]
        arity = {'Var': 1, 'Let': 3, 'VarBind': 3, 'Assign': 2, 'Rec': 3, 'RecV': 3,
                 'App': 2, 'Val': 1, 'LitV': 1, 'LitInt': 1, 'LitBool': 1,
                 'LitPtr': 1, 'LitObj': 1, 'LitStack': 1, 'LitUnit': 0, 'LitNull': 0,
                 'Load': 1, 'Store': 2, 'Alloc': 1, 'Free': 1, 'Offset': 2,
                 'Seq': 2, 'If': 3, 'While': 2, 'BinOp': 3, 'Struct': 2, 'StructV': 1,
                 'New': 2, 'StructLoad': 2, 'StructStore': 3, 'FieldLoad': 2, 'FieldStore': 3,
                 'StackLoad': 1, 'StackAssign': 2, 'StackFieldStore': 3, 'Pop': 2}
        if name not in arity or len(args) != arity[name]:
            return None
        term = lambda n: self.host.term(n, env)
        if name in ('Val', 'LitV', 'LitInt', 'LitBool'):
            return term(args[0])
        if name in ('LitUnit', 'LitNull'):
            return leaf('unit' if name == 'LitUnit' else 'null')
        if name in ('LitPtr', 'LitObj', 'LitStack'):
            return call({'LitPtr': 'pointer', 'LitObj': 'object', 'LitStack': 'slot'}[name], [term(args[0])])
        if name == 'Var':
            spelling = self.string(args[0])
            return self.variable(spelling) if spelling is not None else self.unsupported(key, args, env, 'symbolic variable name')
        if name in ('Rec', 'RecV'):
            return self.function(key, args, env)
        if name in ('Let', 'VarBind'):
            if name == 'Let':
                ok, spelling = self.optional(args[0])
            else:
                spelling = self.string(args[0])
                ok = spelling is not None
            if not ok:
                return self.unsupported(key, args, env, 'symbolic binding name')
            token = self.fresh(spelling, env) if spelling is not None else None
            function = self.initializer_function(args[1]) if token else None
            if function:
                initializer = self.function(*function, env, binding=token, mutable=name == 'VarBind')
            elif token:
                value = term(args[1])
                keyword = 'let' if name == 'Let' else 'var'
                initializer = phrase(keyword + ' {0} = {1}', [Doc(token), value]) if value.inline() is not None else phrase(keyword + ' {0} =\n  {1}', [Doc(token), value])
            else:
                initializer = term(args[1])
            with self.scope({spelling: token} if token else {}):
                body = term(args[2])
            return sequence(initializer, body)
        if name in ('Assign', 'StructStore'):
            spelling = self.string(args[0])
            if spelling is None:
                return self.unsupported(key, args, env, 'symbolic assignment target')
            target = self.variable(spelling)
            if name == 'StructStore':
                return phrase('store {0} in {1}', [term(args[2]), call('item', [target, term(args[1])])])
            return phrase('{0} = {1}', [target, term(args[1])])
        if name == 'App':
            return phrase('{0}({1})', [term(args[0]), term(args[1])], atomic=True)
        if name in ('Load', 'StackLoad'):
            return phrase('load at {0}', [term(args[0])])
        if name in ('Store', 'StackAssign'):
            return phrase('store {0} at {1}', [term(args[1]), term(args[0])])
        if name in ('Alloc', 'Free', 'Offset'):
            return call({'Alloc': 'allocate', 'Free': 'free', 'Offset': 'pointer_offset'}[name], [term(a) for a in args])
        if name == 'Seq':
            return sequence(term(args[0]), term(args[1]))
        if name == 'If':
            return phrase('if {0}:\n  {1}\nelse:\n  {2}', [term(a) for a in args])
        if name == 'While':
            return phrase('while {0}:\n  {1}', [term(a) for a in args])
        if name == 'BinOp':
            operator, operands = self.app(args[0])
            if not operands and operator and operator.startswith(CJR) and operator[len(CJR):] in OPERATORS:
                return phrase('{0} ' + OPERATORS[operator[len(CJR):]] + ' {1}', [term(args[1]), term(args[2])])
            return None
        if name in ('Struct', 'StructV', 'New'):
            lists = [self.listing(a) for a in args]
            if all(xs is not None for xs in lists):
                return call('new object' if name == 'New' else 'struct', [term(a) for xs in lists for a in xs])
            labels = ['values', 'pending expressions'] if len(args) == 2 else ['values']
            return Doc(Token('new object' if name == 'New' else 'struct'),
                       [Doc(Token(label), [term(a)], block=True) for label, a in zip(labels, args)], block=True, plain_indent=2)
        if name in ('FieldLoad', 'StructLoad'):
            return call('field' if name == 'FieldLoad' else 'item', [term(a) for a in args])
        if name in ('FieldStore', 'StackFieldStore'):
            target = term(args[0])
            if name == 'StackFieldStore':
                target = phrase('load at {0}', [target])
            return phrase('store {0} in {1}', [term(args[2]), call('field' if name == 'FieldStore' else 'item', [target, term(args[1])])])
        return self.unsupported(key, args, env, 'explicit stack lifetime operation')


def uses_rel(node, index=1):
    """Whether a native term uses the outer binder, accounting for nested binders."""
    if isinstance(node, list):
        return any(uses_rel(n, index) for n in node)
    if not isinstance(node, dict):
        return False
    tag = node.get('tag')
    if tag == 'rel':
        return node['index'] == index
    if tag in ('lambda', 'product', 'let'):
        return any(uses_rel(v, index + (key == 'body')) for key, v in node.items())
    if tag in ('fix', 'cofix'):
        count = len(node['definitions'])
        return any(uses_rel(d['type'], index) or uses_rel(d['body'], index + count) for d in node['definitions'])
    return any(uses_rel(v, index) for v in node.values())
