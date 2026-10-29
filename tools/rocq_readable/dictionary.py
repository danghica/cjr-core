"""Validated declarative templates; no HTML, evaluation, or dropped slots."""
from __future__ import annotations

import json
from pathlib import Path

from .layout import Doc, Token, template_parts


class DictionaryError(ValueError):
    pass


def validate(rule):
    if not isinstance(rule, dict) or set(rule) - {"kind", "key", "arity", "scope", "entry", "identity", "label", "layout", "slots", "template", "when"}:
        raise DictionaryError("rule contains unknown fields")
    if rule.get("kind") not in ("application", "notation"):
        raise DictionaryError("kind must be application or notation")
    for name in ("key", "label"):
        if not isinstance(rule.get(name), str) or not rule[name] or any(c in rule[name] for c in "\n\r\t"):
            raise DictionaryError(f"{name} must be a nonempty, single-line string")
    arity = rule.get("arity")
    if type(arity) is not int or arity < 0:
        raise DictionaryError("arity must be a nonnegative integer")
    if rule.get("layout", "call") not in ("call", "block"):
        raise DictionaryError("layout must be call or block")
    for name in ("scope", "entry", "identity"):
        if name in rule and rule[name] is not None and not isinstance(rule[name], str):
            raise DictionaryError(f"{name} must be a string or null")
    slots = rule.get("slots", list(range(arity)))
    if not isinstance(slots, list) or any(type(x) is not int for x in slots) or sorted(slots) != list(range(arity)):
        raise DictionaryError("slots must contain each argument/binder placeholder exactly once")
    if "when" in rule and rule["when"] != "proposition":
        raise DictionaryError("when must be proposition")
    if "template" in rule:
        text = rule["template"]
        if not isinstance(text, str) or not text or any((ord(c) < 32 and c != "\n") or ord(c) == 127 for c in text):
            raise DictionaryError("template must be nonempty plain text with spaces for indentation")
        try:
            placeholders = [p for p in template_parts(text) if isinstance(p, int)]
        except ValueError as exc:
            raise DictionaryError(str(exc)) from exc
        if sorted(placeholders) != list(range(arity)):
            raise DictionaryError("template must contain each numbered slot exactly once")
        if any((len(line) - len(line.lstrip(" "))) % 4 for line in text.splitlines()):
            raise DictionaryError("template indentation must use multiples of four spaces")
    return {**rule, "layout": rule.get("layout", "call"), "slots": slots}


def selector(rule):
    return tuple(rule.get(k) for k in ("kind", "key", "arity", "scope", "entry", "identity"))


class Dictionary:
    def __init__(self, path: Path):
        self.path = path
        self.rules = []
        if path.exists():
            try:
                data = json.loads(path.read_text())
            except (OSError, ValueError) as exc:
                raise DictionaryError(f"cannot read dictionary {path}: {exc}") from exc
            if not isinstance(data, dict) or set(data) != {"version", "rules"} or data["version"] != 1 or not isinstance(data["rules"], list):
                raise DictionaryError("dictionary must contain version: 1 and a rules array")
            self.rules = [validate(rule) for rule in data["rules"]]
            if len({selector(r) for r in self.rules}) != len(self.rules):
                raise DictionaryError("duplicate dictionary selectors")

    def match(self, kind, key, arity, scope=None, entry=None, identity=None):
        matches = [rule for rule in self.rules if rule["kind"] == kind and rule["key"] == key and
                   rule["arity"] == arity and ("scope" not in rule or rule["scope"] == scope) and
                   ("entry" not in rule or rule["entry"] == entry) and
                   ("identity" not in rule or rule["identity"] == identity)]
        if not matches:
            return None
        specificity = max(sum(k in r for k in ("scope", "entry", "identity")) for r in matches)
        winners = [r for r in matches if sum(k in r for k in ("scope", "entry", "identity")) == specificity]
        if len(winners) != 1:
            raise DictionaryError(f"ambiguous rendering rules for {key!r}")
        return winners[0]

    def apply(self, rule, original: Token, children, proposition=False):
        label = Token(rule["label"], identity=original.identity, local=original.local)
        template = rule.get("template") if rule.get("when") != "proposition" or proposition else None
        return Doc(label, [children[i] for i in rule["slots"]], block=rule["layout"] == "block", template=template)

    def replace(self, rule):
        rule = validate(rule)
        self.rules = [old for old in self.rules if selector(old) != selector(rule)] + [rule]

    def remove(self, rule):
        self.rules = [old for old in self.rules if selector(old) != selector(rule)]

    def save(self):
        self.path.parent.mkdir(parents=True, exist_ok=True)
        data = {"version": 1, "rules": sorted(self.rules, key=lambda r: json.dumps(selector(r)))}
        temporary = self.path.with_name(self.path.name + ".tmp")
        temporary.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")
        temporary.replace(self.path)
