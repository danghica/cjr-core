---
name: cjr-spec-core
description: Read an application-core prompt, check that it describes a hexagonal core without explicit system interactions, invite algebraic validation properties when absent, and present a specification plan for a later cjr-build-core handoff. Use when a contributor asks to specify or plan a CJR application core; this skill does not implement the plan.
---

# Specify a CJR application core

Guide the contributor through the following conversation. Keep the current
specification prompt and its revisions together throughout the interaction.
Generate a plan only after the architectural checks pass and the optional
algebraic-property discussion is resolved. Do not implement the plan.

## Read the core prompt

Ask the user exactly:

> Please describe the core of the app you want built. Remember that this platform uses the hexagonal (aka p&a) architecture, so the core you are specifying must not include any explicit system interactions. It is pure business logic. 

Wait for their description. If they already supplied a core description when
invoking this skill, use it as their response rather than asking them to repeat
it. Read the entire prompt, including any supplied specification file, before
evaluating it.

## Check the hexagonal boundary

Determine whether the prompt describes domain data, rules, operations, and
state transitions independently of explicit system interactions. The core may
accept ordinary input values and return values or updated domain state.

Explicit filesystem access, database operations, network requests, UI actions,
process execution, and direct clock or random-generator calls belong outside
this core. Externally obtained values can instead be passed into pure domain
operations. Mentioning that adapters exist outside the core is acceptable;
requiring the core itself to execute those interactions is not.

If the prompt violates this boundary, identify the concrete interactions at
issue and ask the user to reformulate it as a hexagonal core. If the boundary
is ambiguous, ask a focused question. Wait for their response and repeat this
check before proceeding. Offer guidance, but do not silently change their
requirements, invent an adapter design, or proceed on an unresolved assumption.

## Invite algebraic validation properties

Once the architecture is acceptable, examine whether the prompt includes
validation of the specification expressed as algebraic properties of its
operations or state. These are general laws over admissible inputs or sequences
of operations, such as identity, inverse, composition, idempotence, or
preservation of an invariant. Example input/output cases or a generic request
to test the app do not by themselves supply algebraic properties.

If such properties are already present, retain them and proceed to the final
architecture check. If they are absent, ask the user exactly:

> It is useful to include in your specification validation (algebraic) properties of the specification. Would you like to?

Wait for their answer; elapsed time is not an answer.

- If yes, ask them to provide the properties unless they included them in the
  same response. Read the properties and append them to the previous prompt,
  preserving the earlier requirements and their wording. Retain them as an
  identifiable addition rather than replacing the original description.
- If no, continue with the original prompt and record that algebraic validation
  properties were declined. Do not invent properties on the user's behalf.
- If the answer is unclear, clarify it before proceeding.

Resolve unclear property statements with the user so that the plan can express
their intended laws and any necessary preconditions. Do not silently weaken a
law or treat an apparently contradictory set of laws as a validated contract.

## Re-examine the complete prompt

Re-read the entire current prompt, including appended properties and all
reformulations. Check again that it describes a valid hexagonal core. A property
that requires an explicit system interaction also needs clarification.

If it is invalid or ambiguous, explain the remaining issue and refer back to the
user for help. Wait for their correction, then re-examine the updated prompt.
If a revision removes the previously supplied properties, return to the
algebraic-property question unless the user has already declined them. Proceed
only once the current prompt is a valid hexagonal-core description.

## Generate and present the plan

Present a concrete specification plan based on the accepted prompt. Include:

- The core's purpose and architectural boundary.
- Domain data and state, operations, inputs, outputs, and relevant preconditions
  or error outcomes, to the extent specified by the user.
- The supplied algebraic validation properties and the operations each law
  constrains, or the user's decision to omit them.
- An ordered plan for specifying the core and validating the supplied laws,
  with acceptance criteria traceable to the accepted prompt.
- Remaining nonblocking questions, clearly distinguished from agreed
  requirements. Resolve questions that prevent a coherent specification before
  presenting the final plan.

Retain the accepted prompt and appended properties alongside the plan in the
conversation so they are available for the later handoff. Do not add implementation
code, run builds, generate application files, or treat the plan as authorization
to implement it.

State that the plan requires the `cjr-build-core` skill for implementation.
Do not invoke it automatically: the deliverable here is the presented plan,
and implementation begins when the user requests that handoff. If
`cjr-build-core` is unavailable, retain the completed plan and identify the
missing skill without invoking a substitute.
