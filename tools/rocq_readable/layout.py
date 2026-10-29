"""A semantic document tree: links survive layout and user templates."""
from __future__ import annotations

from dataclasses import dataclass, field
import html
import hashlib
from pathlib import Path
import os
import string
from urllib.parse import quote


def template_parts(text):
    """Literal text and integer slots; braces are escaped as {{ and }}."""
    parts = []
    for literal, name, spec, conversion in string.Formatter().parse(text):
        if literal:
            parts.append(literal)
        if name is not None:
            if not name.isascii() or not name.isdecimal() or spec or conversion:
                raise ValueError("template placeholders must be numbered slots, e.g. {0}")
            parts.append(int(name))
    return parts


@dataclass(frozen=True)
class Token:
    text: str
    identity: str | None = None
    anchor: str | None = None
    local: str | None = None
    css: str = ""


@dataclass
class Doc:
    label: Token
    children: list[Doc] = field(default_factory=list)
    block: bool = False
    raw: bool = False
    template: str | None = None

    def literal(self, text):
        return Token(text, identity=self.label.identity, local=self.label.local)

    def argument(self, child):
        tokens = child.inline()
        # Parentheses make nested custom operators unambiguous. Transparent
        # wrappers inherit their child's grouping requirement.
        if tokens is not None and child.compound():
            return [Token("("), *tokens, Token(")")]
        return tokens

    def compound(self):
        if self.template is None:
            return False
        parts = template_parts(self.template)
        if len(parts) == 1 and isinstance(parts[0], int):
            return self.children[parts[0]].compound()
        return bool(self.children)

    def inline(self):
        if self.block or self.raw and "\n" in self.label.text or self.template is not None and "\n" in self.template:
            return None
        if self.template is not None:
            parts = template_parts(self.template)
            if len(parts) == 1 and isinstance(parts[0], int):
                return self.children[parts[0]].inline()
            tokens = []
            for part in parts:
                if isinstance(part, str):
                    tokens.append(self.literal(part))
                else:
                    child = self.argument(self.children[part])
                    if child is None:
                        return None
                    tokens.extend(child)
            return tokens
        parts = [child.inline() for child in self.children]
        if any(part is None for part in parts):
            return None
        if not self.children:
            return [self.label]
        tokens = [self.label, Token("(")]
        for i, part in enumerate(parts):
            if i:
                tokens.append(Token(", "))
            tokens.extend(part)
        return [*tokens, Token(")")]

    def lines(self, indent=0, width=92):
        inline = self.inline()
        if inline is not None and indent * 4 + sum(len(t.text) for t in inline) <= width:
            return [(indent, inline)]
        if self.template is not None:
            lines = []
            for text in self.template.split("\n"):
                spaces = len(text) - len(text.lstrip(" "))
                level = indent + spaces // 4
                pending = []
                parts = template_parts(text[spaces:])
                for part in parts:
                    if isinstance(part, str):
                        pending.append(self.literal(part))
                        continue
                    child = self.children[part]
                    tokens = child.inline() if len(parts) == 1 else self.argument(child)
                    if not self.block and tokens is not None and (level * 4 + sum(len(t.text) for t in pending + tokens) <= width):
                        pending.extend(tokens)
                    else:
                        if pending:
                            lines.append((level, pending))
                        child_level = level + 1 if pending or self.block else level
                        if len(parts) > 1 and child.compound():
                            lines.append((child_level, [Token("(")]))
                            lines.extend(child.lines(child_level + 1, width))
                            lines.append((child_level, [Token(")")]))
                        else:
                            lines.extend(child.lines(child_level, width))
                        pending = []
                if pending or not text:
                    lines.append((level, pending))
            return lines
        if self.raw:
            return [(indent, [Token(line, css="unsupported")]) for line in self.label.text.splitlines()]
        if not self.children:
            # A long identifier or literal is a single unbreakable token.
            return [(indent, [self.label])]
        return [(indent, [self.label, Token(":")]),
                *(line for child in self.children for line in child.lines(indent + 1, width))]

    def plain(self):
        return "\n".join("    " * level + "".join(t.text for t in tokens) for level, tokens in self.lines())


def leaf(text, **kwargs):
    return Doc(Token(text, **kwargs))


def anchor(identity: str):
    # ASCII anchors avoid URL-fragment decoding differences for Unicode
    # names and Rocq's notation identities.
    return "symbol-" + hashlib.sha256(identity.encode()).hexdigest()[:24]


def tokens_html(tokens, current: Path, symbols: dict[str, tuple[Path, str]]):
    result = []
    for token in tokens:
        text = html.escape(token.text)
        if token.identity and token.identity in symbols:
            target, target_anchor = symbols[token.identity]
            relative = "" if target == current else quote(os.path.relpath(target, current.parent).replace(os.sep, "/"), safe="/")
            text = f'<a href="{relative}#{target_anchor}" title="{html.escape(token.identity, quote=True)}">{text}</a>'
        elif token.local:
            text = f'<a href="#{html.escape(token.local, quote=True)}">{text}</a>'
        elif token.identity:
            text = f'<span class="external" title="External or unresolved: {html.escape(token.identity, quote=True)}">{text}</span>'
        if token.anchor:
            text = f'<span id="{html.escape(token.anchor, quote=True)}">{text}</span>'
        if token.css:
            text = f'<span class="{html.escape(token.css, quote=True)}">{text}</span>'
        result.append(text)
    return "".join(result)


def render_html(doc: Doc, current, symbols):
    return "\n".join("    " * level + tokens_html(tokens, current, symbols)
                     for level, tokens in doc.lines())
