"""Display-only ownership wording; legacy explanation documents stay unchanged."""
from dataclasses import replace

from .layout import Doc, Token

FORMS = {
    'owns_raw': (2, 'owns {0} ↦ {1}'),
    'owns_stack': (2, 'owns slot {0} ↦ {1}'),
    'owns_object_field': (3, 'owns field {1} of {0}'),
    'owns_block': (2, 'owns block {0} of length {1}'),
}


def references(document):
    """A second mention links to the original binder instead of defining it twice."""
    token = document.label
    if token.anchor:
        token = replace(token, anchor=None, local=token.anchor)
    return replace(document, label=token, children=[references(c) for c in document.children])


def skin(document, details):
    children = [skin(child, details) for child in document.children]
    doc = replace(document, children=children)
    form = FORMS.get(doc.label.text)
    if doc.raw or doc.template is not None or form is None or len(children) != form[0]:
        return doc
    if doc.label.text == 'owns_object_field':
        # The requested surface form omits the contents, but they remain auditable.
        details.append(Doc(Token(''), [references(children[0]), references(children[1]), children[2]],
                           template='field {1} of {0} stores {2}', plain_indent=2))
    return replace(doc, label=replace(doc.label, text='owns'), template=form[1],
                   block=False, template_indent=2, plain_indent=2)
