/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.Galois.IntegralClosure

@[expose] public section

/-!
# Branch invariants of a Galois integral closure

This leaf packages the common ramification index, inertia degree, and fundamental identity for
the maximal branches of a finite Galois extension of the fraction field of a discrete valuation
ring.  It uses the canonical `FractionRing A`, so callers do not have to rebuild integral-closure
or Galois-group instances locally.

@stack 09EB
-/

open Ideal IsLocalRing
open scoped Pointwise

universe u w

namespace integralClosure.Ramification

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {L : Type w} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable [FiniteDimensional (FractionRing A) L] [IsGalois (FractionRing A) L]

/-- Every maximal branch has the common ramification index of the Galois integral closure. -/
@[stacks 09EB "common ramification index of Galois integral-closure branches"]
theorem ramificationIdx_eq_ramificationIdxIn
    (P : (maximalIdeal A).primesOver (integralClosure A L)) :
    P.1.ramificationIdx A =
      (maximalIdeal A).ramificationIdxIn (integralClosure A L) := sorry

-- Proof strategy: specialize `Ideal.ramificationIdxIn_eq_ramificationIdx` to
-- `p := maximalIdeal A`, `P`, and `G := Gal(L/(FractionRing A))`, using the canonical
-- `integralClosure.isGaloisGroup` instance, then reverse the resulting equality.

/-- Every maximal branch has the common inertia degree of the Galois integral closure. -/
@[stacks 09EB "common inertia degree of Galois integral-closure branches"]
theorem inertiaDeg_eq_inertiaDegIn
    (P : (maximalIdeal A).primesOver (integralClosure A L)) :
    P.1.inertiaDeg A =
      (maximalIdeal A).inertiaDegIn (integralClosure A L) := sorry

-- Proof strategy: apply `Ideal.inertiaDegIn_eq_inertiaDeg` to the same canonical Galois action
-- and branch `P`, then use symmetry to match the source-facing orientation.

/-- The common ramification index of the maximal branches is positive. -/
@[stacks 09EB "positivity of the common ramification index"]
theorem one_le_ramificationIdxIn :
    1 ≤ (maximalIdeal A).ramificationIdxIn (integralClosure A L) := sorry

-- Proof strategy: obtain nonvanishing from `Ideal.ramificationIdxIn_ne_zero` with
-- `G := Gal(L/(FractionRing A))`; the finite and faithful integral-closure module structures are
-- canonical here.  Convert the nonzero natural number to the stated inequality with
-- `Nat.one_le_iff_ne_zero`.

/-- The common inertia degree of the maximal branches is positive. -/
@[stacks 09EB "positivity of the common inertia degree"]
theorem one_le_inertiaDegIn :
    1 ≤ (maximalIdeal A).inertiaDegIn (integralClosure A L) := sorry

-- Proof strategy: use `Ideal.inertiaDegIn_ne_zero` for the canonical Galois group action on the
-- integral closure and conclude with `Nat.one_le_iff_ne_zero`.

/-- The degree of the Galois extension is the number of maximal branches times their common
ramification index and inertia degree. -/
@[stacks 09EB "fundamental identity for a Galois integral closure"]
theorem fundamentalIdentity :
    Module.finrank (FractionRing A) L =
      ((maximalIdeal A).primesOver (integralClosure A L)).ncard *
        ((maximalIdeal A).ramificationIdxIn (integralClosure A L) *
          (maximalIdeal A).inertiaDegIn (integralClosure A L)) := sorry

-- Proof strategy: apply
-- `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn` to the canonical
-- `Gal(L/(FractionRing A))` action on `integralClosure A L`.  Rewrite `Nat.card Gal` as
-- `Module.finrank (FractionRing A) L` via `IsGalois.card_aut_eq_finrank`, then reverse the
-- equality to match the source convention.

end integralClosure.Ramification
