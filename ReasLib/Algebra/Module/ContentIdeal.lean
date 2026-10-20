/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Content ideals of module elements

The predicate is defined without a flatness assumption: leastness of an ideal
supporting an element makes sense for every module. Existence and stability
results that require flatness live in separate leaves.

@stack 0ASA
-/

universe u v

variable {A : Type u} {M : Type v}
variable [CommSemiring A] [AddCommMonoid M] [Module A M]

/-- Definition 15.24.1, tag `0ASA`: `I` is a content ideal of `x` when it is
the least ideal whose multiple of the ambient module contains `x`.

The source introduces the notion for flat modules; the definition itself does
not use flatness, so the reusable owner is stated at the natural module level. -/
@[stacks 0ASA "content ideals of module elements"]
def IsContentIdeal (x : M) (I : Ideal A) : Prop :=
  IsLeast { J : Ideal A | x ∈ J • (⊤ : Submodule A M) } I

namespace IsContentIdeal

/-- Content-ideal leastness consists of membership in `I M` and minimality
among all ideals whose multiples contain the element. -/
@[stacks 0ASA "content ideal membership and minimality"]
theorem iff {x : M} {I : Ideal A} :
    IsContentIdeal x I ↔
      x ∈ I • (⊤ : Submodule A M) ∧
        ∀ {J : Ideal A}, x ∈ J • (⊤ : Submodule A M) → I ≤ J := sorry
-- Proof strategy: unfold `IsContentIdeal`, `IsLeast`, and `lowerBounds`; membership in the set
-- comprehension reduces both clauses definitionally.

/-- An element belongs to the multiple of its content ideal. -/
@[stacks 0ASA "content ideal contains its element"]
theorem mem {x : M} {I : Ideal A} (hI : IsContentIdeal x I) :
    x ∈ I • (⊤ : Submodule A M) := sorry
-- Proof strategy: take the membership component of `iff.mp hI`.

/-- A content ideal is contained in every ideal whose module multiple contains
the element. -/
@[stacks 0ASA "content ideal minimality"]
theorem le {x : M} {I J : Ideal A} (hI : IsContentIdeal x I)
    (hx : x ∈ J • (⊤ : Submodule A M)) : I ≤ J := sorry
-- Proof strategy: apply the minimality component of `iff.mp hI` to `hx`.

/-- A module element has at most one content ideal. -/
@[stacks 0ASA "uniqueness of content ideals"]
theorem unique {x : M} {I J : Ideal A} (hI : IsContentIdeal x I)
    (hJ : IsContentIdeal x J) : I = J := sorry
-- Proof strategy: unfold `IsContentIdeal` in both hypotheses and apply `IsLeast.unique`.

end IsContentIdeal
