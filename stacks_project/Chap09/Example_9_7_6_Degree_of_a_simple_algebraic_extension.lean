/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdjoinRoot
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

universe u

section

variable {k : Type u} [Field k]

/- Domain-style sampling for Example 9.7.6:
- `source-facing`: the degree of the simple extension `k[t]/(P)`
- `core/canonical`: `finrank_quotient_span_eq_natDegree`
- `bridge/view`: `AdjoinRoot.instField`, which uses irreducibility to view the same quotient as a
  field

Primitive data is only the polynomial quotient. The irreducibility hypothesis belongs to the
derived field/simple-extension interface, not to a duplicate local degree theorem.
-/

/- Example 9.7.6 (Degree of a simple algebraic extension): once `P` is irreducible, Example 9.3.3
supplies the field structure on `k[X] ⧸ Ideal.span {P}`. The degree computation itself is the
canonical theorem `finrank_quotient_span_eq_natDegree`. -/
@[stacks 09G7]
#check finrank_quotient_span_eq_natDegree

end

-- Example 9.7.2 context (degree-2 extension `ℂ/ℝ`): owned by `Example_9_7_2.lean`
-- (`Complex.finrank_real_complex`, Tag 09G4); the clone formerly here was removed for reuse.
