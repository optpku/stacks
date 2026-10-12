/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.Ideal.Span
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

universe u

noncomputable section

section

variable {k : Type u} [Field k]

/-
Domain-style sampling for Example 9.6.4:
- primary domain: simple algebraic extensions presented by adjoining a root of a polynomial;
- sampled owner API:
  `AdjoinRoot`,
  `AdjoinRoot.instField`,
  `AdjoinRoot.instAlgebra`,
  `finrank_quotient_span_eq_natDegree`;
- best owner abstraction: the quotient owner `AdjoinRoot P`, with its canonical field and
  `k`-algebra structures supplied upstream.

Primitive-vs-derived split:
- primitive data: the polynomial `P : k[X]` and the quotient owner `AdjoinRoot P`;
- derived API: the field structure under irreducibility and the ambient `k`-algebra structure.

Source/core/bridge triage:
- `source-facing`: the simple extension `k[t]/(P)` viewed as an extension field of `k`;
- `core/canonical`: `AdjoinRoot`, `AdjoinRoot.instField`, `AdjoinRoot.instAlgebra`;
- `bridge/view`: the quotient spelling `k[X] ⧸ Ideal.span {P}` from Example 9.3.3.

This example adds no new data, so the canonical owner instances should be recalled directly, with
the quotient spelling used only as a source-facing bridge check.
-/

section

variable (P : k[X]) [Fact (Irreducible P)]

/- Example 9.6.4: the simple extension `k[t]/(P)` is formalized by `AdjoinRoot P`, which is
definitionally the quotient `k[X] ⧸ Ideal.span {P}`. For irreducible `P`, the canonical
instance `AdjoinRoot.instField` from Example 9.3.3 makes it a field. -/
@[stacks 09FX]
#check AdjoinRoot.instField

end

section
variable (P : k[X])

/- The canonical owner instance for the adjoin-root construction is `AdjoinRoot.instAlgebra`. -/
#check AdjoinRoot.instAlgebra

/- Therefore the quotient spelling `k[X] ⧸ Ideal.span {P}` inherits the same canonical
`k`-algebra structure. Together with the field instance above, this exhibits `k[t]/(P)` as an
extension of `k`. -/
#check (inferInstance : Algebra k (k[X] ⧸ Ideal.span {P}))

end

end
