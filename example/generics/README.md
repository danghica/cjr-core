# Generic CJR programs

CJR supports explicit, unconstrained rank-one generic functions, classes,
structs, and methods through an erased source layer. `generic_examples.v`
contains both the program definitions and their Iris specifications. The same
source definitions generate `extracted/generics.cj`.

The examples are `genericId<T>`, `Pair<A, B>` with construction and projections,
and `Box<T>` with construction, `get`, and `map<U>`. Additional cases exercise
identical function bodies, equal-sized layouts, nested instances, typed
callbacks, and direct generic recursion. The class parameter `T` and method
parameter `U` have separate scopes; shadowing is rejected.

## Building and checking

From the repository root, with the Rocq toolchain on `PATH`:

```sh
make -C example/generics build
make -C example/generics test
make verify
```

The test target extracts the aggregate bundle, compiles with Cangjie 1.0.5,
and runs ten test cases. Results and compiler output are in `test/results/`.
`generic_tests.v` contains kernel-checked extraction and scoping regressions.
The test target also runs three compiler-rejection regressions: unrelated
receiver layouts, wrong receiver type arguments, and wrong lambda result types.

## Defining programs

`gty` represents `Int64`, `Bool`, `Unit`, scoped type variables, named type
applications, and unary function types. `gexpr` represents expressions,
explicit generic calls, constructors, fields, methods, and typed lambdas.
`gfunction` records type parameters, ordinary parameters, return type, and body.
A method's first source parameter is its receiver; extraction renders it as
`this`. `glayout` records a named class or struct and its ordered fields.

Every call supplies its type arguments explicitly, including calls from one
generic function to another. Declare function dependencies before their users;
direct self recursion is supported, while forward references and mutual
recursion are rejected. Callbacks use typed lambdas; wrap a named generic call
in a lambda when passing it as a callback. Bare named function values are
rejected by this first version.

Constructors and receiver annotations name their layout explicitly. Native
receiver type checks prevent annotations for two different layouts with common
field names from disagreeing about which field is selected. Locals cannot hide
declaration names. Internal argument binders are unavailable to source code.

The generic expression fragment includes immutable bindings, lambdas,
conditionals, integer/Boolean operations, struct construction and projection,
and class allocation and reading. Existing mutable/raw-memory programs remain
available through the original CJR language and printer. `GECore` embeds an
existing CJR term into the generic logic exactly; generic extraction rejects
that escape hatch, so use the legacy printer for those terms.

## What is proved

`erase` translates a source expression into the existing operational language.
Named declarations link to CJR recursive values; calls evaluate argument tuples
from left to right. Types disappear. Boolean conjunction evaluates both operands, matching CJR; the
printer uses an eager helper rather than native short-circuit evaluation. `erase_instantiate` proves that replacing
type variables does not alter the erased program when receiver annotations
name layouts. `erase_subst` proves compatibility with local value substitution
when referenced declarations are closed for that variable.

`generic_wp` is the existing Iris weakest precondition applied to erasure.
`generic_wp_legacy` and `erase_legacy` express conservative inclusion of every
old program and specification. `generic_adequacy` uses the existing CJR
adequacy theorem to establish safety of erased programs. No new runtime state
or Iris ghost resources are introduced.

Identity, pair construction/projections, and box construction/reading have
uniform contracts parameterised by arbitrary Iris predicates on values.
`box_map_spec` requires a closed callback satisfying a supplied WP contract.
The callback consumes the input representation and supplies the output
representation. The old box's field ownership is retained; its element
representation is not duplicated. Persistent representations can be shared
using the usual Iris rules. The closed `generic_main_adequate` theorem checks
an extracted identity client returning 42.

## Validation boundary

The generic extractor checks identifier and type-variable scope, nominal type
arities, function/method/constructor arities, field indexes, method receivers,
and unsupported forms before returning `Extracted`. Its result otherwise
contains diagnostics. This structural checker is not a complete static type
system: Cangjie compilation checks ordinary argument/result type compatibility.

The Rocq kernel checks erasure laws and Iris contracts, and `make verify`
audits their assumptions. Runtime tests check the generated source against
the native compiler. The printer and Cangjie toolchain remain part of the
translation trust boundary; there is no verified Cangjie compiler or universal
relational-parametricity theorem here. CJR's existing unbounded-integer versus
`Int64` overflow obligations still apply.

Interface bounds, higher-rank polymorphism, inheritance, generic raw-memory
allocation, and conversion of the existing containers are deferred.
