"""Evaluate the repository's Gallina Cangjie printer in isolated Rocq states."""
from __future__ import annotations

import re

from .ast import identifier, value
from .backend import Backend, BackendError
from .project import Glob, Source, configuration

IMPORTS = ('From Coq Require Import String Ascii List. '
           'From cjr.examples Require Import cj_print. '
           'Open Scope string_scope. Set Printing Width 1000000. '
           'Set Printing Depth 1000000. ')
EMPTY = 'cj_print.Env nil nil nil None nil nil nil false cj_print.no_copy_rules'


def fresh(source):
    """Never substitute a compiled declaration for edited source."""
    compiled = source.path.with_suffix('.vo')
    return (not source.errors and compiled.is_file()
            and compiled.stat().st_mtime_ns >= source.path.stat().st_mtime_ns
            and Glob.load(source.path, source.text.encode()).valid)


def request(backend, source, command, offset=None):
    prefix = source.text.encode()[:offset].decode() if offset is not None else source.text
    lines = prefix.split('\n')
    return backend.request('petanque/run_at_point', {
        'textDocument': {'uri': source.path.as_uri(), 'version': 1},
        'position': {'line': len(lines) - 1,
                     'character': len(lines[-1].encode('utf-16-le')) // 2},
        'command': command})


def names(decl):
    result = []
    for binder in decl.binders:
        parts = value(binder)
        if parts and parts[0] == 'CLocalAssum':
            result.extend(identifier(n) for n in parts[1])
    return result


def printing_command(identity, arguments, env):
    # Identifiers originate in Rocq's AST; strings still need Rocq escaping.
    quoted = lambda s: '"' + s.replace('"', '""') + '"'
    ns = '(nil : list string)'
    for name in reversed(arguments):
        ns = '(cons ' + quoted(name) + ' ' + ns + ')'
    return IMPORTS + f'''Goal True.
let rec unavailable T :=
  let T := eval hnf in T in
  lazymatch T with
  | cjr.lang.expr => idtac "CJR-UNAVAILABLE"
  | cjr.lang.val => idtac "CJR-UNAVAILABLE"
  | cj_print.prog => idtac "CJR-UNAVAILABLE"
  | cj_print.decl => idtac "CJR-UNAVAILABLE"
  | cj_print.fn => idtac "CJR-UNAVAILABLE"
  | ?A -> ?B => unavailable B
  | _ => idtac "CJR-NONE"
  end in
let rec render term ns :=
  let T := type of term in
  let T := eval hnf in T in
  lazymatch T with
  | cjr.lang.expr =>
      let s := eval vm_compute in
        (match cj_print.find_body ({env}) term with
         | Some k => cj_print.print_fn ({env}) "" k
         | None => cj_print.ex ({env}) "" term end) in idtac s
  | cjr.lang.val => let s := eval vm_compute in (cj_print.exv ({env}) "" term) in idtac s
  | cjr.lang.base_lit => let s := eval vm_compute in (cj_print.lit term) in idtac s
  | cj_print.prog => let s := eval vm_compute in (cj_print.print_prog term) in idtac s
  | cj_print.decl => let s := eval vm_compute in (cj_print.print_decl ({env}) "class" term) in idtac s
  | cj_print.fn => let s := eval vm_compute in (cj_print.print_fn ({env}) "" term) in idtac s
  | cjr.lang.expr -> ?B =>
      lazymatch ns with
      | cons ?n ?rest => let next := constr:(term (cjr.lang.Var n)) in render next rest
      | _ => unavailable T
      end
  | _ => unavailable T
  end in
let term := constr:({identity}) in render term {ns}.
Abort.'''


def result_text(response):
    messages = [str(item[1]).strip() for item in response.get('feedback', [])
                if isinstance(item, list) and len(item) == 2]
    for message in messages:
        if message == 'CJR-UNAVAILABLE':
            return {'status': 'unavailable', 'reason': 'The Gallina printer requires concrete non-expression arguments.'}
        if message.startswith('"') and message.endswith('"'):
            # Rocq strings use doubled quotes, including literal newlines.
            text = message[1:-1].replace('""', '"')
            if '/* unsupported:' in text:
                return {'status': 'unavailable', 'reason': 'The Gallina printer reported an unsupported construct or missing layout metadata.'}
            return {'status': 'available', 'text': text}
    return None


def render_source(backend, source, programs=(), imported=False):
    for decl in source.declarations:
        if not decl.body:
            continue
        env = EMPTY
        if programs:
            scores = [(len(common_prefix(decl.identity, p)), p) for p in programs]
            best = max(score for score, _ in scores)
            choices = [p for score, p in scores if score == best]
            if len(choices) == 1:
                p = choices[0]
                env = (f'cj_print.Env (cj_print.p_classes {p}) (cj_print.p_structs {p}) '
                       f'(cj_print.p_fns {p}) None nil nil nil false cj_print.no_copy_rules')
        try:
            offset = None if imported else decl.source_start + len(decl.source.encode())
            response = request(backend, source, printing_command(decl.identity, names(decl), env), offset)
            result = result_text(response)
            if result:
                source.cangjie[decl.identity] = result
        except BackendError:
            # Unavailable printers, open sections, dependent functions and
            # opaque terms retain the ordinary auditable AST presentation.
            continue


def common_prefix(a, b):
    result = []
    for x, y in zip(a.split('.'), b.split('.')):
        if x != y:
            break
        result.append(x)
    return result


def render_compiled(sources, timeout):
    """Share checked program layouts across freshly compiled source modules."""
    if not all(fresh(source) for source in sources):
        return
    groups = {}
    for source in sources:
        if fresh(source):
            groups.setdefault(configuration(source.path, source.root).parent, []).append(source)
    for workspace, group in groups.items():
        text = IMPORTS + '\n' + '\n'.join('Require ' + s.module + '.' for s in group) + '\n'
        path = workspace / '__rocq_readable_printer__.v'
        model = Source(path, workspace, text, '__rocq_readable_printer__', Glob())
        try:
            with Backend(workspace, timeout) as backend:
                _, diagnostics = backend.document(path, text, model=model)
                if any(d.get('severity') == 1 for d in diagnostics):
                    continue
                programs = []
                for source in group:
                    for decl in source.declarations:
                        if decl.body and re.search(r'\bProg\b', source.fragment(decl.body)):
                            try:
                                request(backend, model, 'Check (' + decl.identity + ' : cj_print.prog).')
                                programs.append(decl.identity)
                            except BackendError:
                                pass
                for source in group:
                    # Queries run at the synthetic document's final position,
                    # but results are attached to the original source model.
                    proxy = Source(path, workspace, text, source.module, source.glob,
                                   declarations=source.declarations, cangjie=source.cangjie)
                    render_source(backend, proxy, programs, imported=True)
        except BackendError:
            continue
