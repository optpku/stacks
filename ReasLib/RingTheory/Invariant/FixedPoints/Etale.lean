/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Ideal.Pointwise
public import ReasLib.RingTheory.Invariant.FixedPoints.Subalgebra

@[expose] public section

universe u v

namespace FixedPoints

variable {R : Type u} {G : Type v}
variable [CommRing R] [Group G] [Finite G] [MulSemiringAction G R]

/-- For a finite group action on a commutative ring, the inclusion from the full fixed
subalgebra to the inertia fixed subalgebra is etale on a principal neighborhood of the
contraction of a prime ideal. -/
theorem etaleAt_inertia (q : Ideal R) [q.IsPrime] :
    -- Local instance justification (defeq pin): Localization.Away must use subalgebraAlgebraOfLe as the full-to-inertia fixed-subalgebra inclusion.
    letI : Algebra (FixedPoints.subalgebra ℤ R (⊤ : Subgroup G))
        (FixedPoints.subalgebra ℤ R (q.inertia G)) :=
      FixedPoints.subalgebraAlgebraOfLe (le_top : q.inertia G ≤ (⊤ : Subgroup G))
    ∃ element : FixedPoints.subalgebra ℤ R (q.inertia G),
      element ∉ q.under (FixedPoints.subalgebra ℤ R (q.inertia G)) ∧
      Algebra.Etale (FixedPoints.subalgebra ℤ R (⊤ : Subgroup G))
        (Localization.Away element) := sorry

end FixedPoints
