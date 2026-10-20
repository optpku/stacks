/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import ReasLib.FieldTheory.Galois.IntegralClosure.FixedPoints
public import ReasLib.RingTheory.Ideal.Inertia
public import ReasLib.RingTheory.Invariant.FixedPoints.ResidueField
public import ReasLib.RingTheory.LocalRing.ResidueField.Map

@[expose] public section

/-!
# Residue fields of fixed subalgebras in an integral closure

This leaf owns the base-to-fixed-subalgebra residue algebra.  The contraction to the base DVR is
canonical, while the induced residue-field algebra remains named data rather than a global instance.
@stack 0BU6
-/

universe u v w

open scoped Pointwise

namespace integralClosure.FixedPoints.ResidueField

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type w} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The contraction of a maximal integral-closure branch to every fixed subalgebra lies over the
base maximal ideal. -/
@[stacks 0BU6 "fixed-subalgebra branch lies over the base branch"]
theorem under_liesOver_maximalIdeal
    (H : Subgroup Gal(L / K)) (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    Ideal.LiesOver
      (m.under (FixedPoints.subalgebra A (integralClosure A L) H))
      (IsLocalRing.maximalIdeal A) := sorry

-- Proof strategy: contract `m` first to the fixed subalgebra and then to `A`.  Rewrite this
-- iterated contraction using the canonical fixed-subalgebra inclusion and use the standard
-- integral-closure branch theorem identifying `m.under A` with
-- `IsLocalRing.maximalIdeal A`.

/-- The canonical residue-field algebra from the base branch to a fixed-subalgebra branch. -/
@[implicit_reducible, stacks 0BU6 "base-to-fixed-subalgebra residue algebra"]
noncomputable def algebraOfBase
    (H : Subgroup Gal(L / K)) (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    Algebra
      (IsLocalRing.maximalIdeal A).ResidueField
      (m.under (FixedPoints.subalgebra A (integralClosure A L) H)).ResidueField :=
  -- Local instance justification (defeq pin): the residue map must use the canonical contraction
  -- pair supplied by `under_liesOver_maximalIdeal`.
  letI : Ideal.LiesOver
      (m.under (FixedPoints.subalgebra A (integralClosure A L) H))
      (IsLocalRing.maximalIdeal A) :=
    under_liesOver_maximalIdeal H m
  Ideal.ResidueField.algebraOfLiesOver
    (IsLocalRing.maximalIdeal A)
    (m.under (FixedPoints.subalgebra A (integralClosure A L) H))

/-- The residue-field map at the decomposition fixed subalgebra is bijective over the base. -/
@[stacks 0BU6 "decomposition residue-field map over the base is bijective"]
theorem baseMap_bijective
    (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    letI : Algebra
        (IsLocalRing.maximalIdeal A).ResidueField
        (m.under
          (FixedPoints.subalgebra A (integralClosure A L)
            (MulAction.stabilizer Gal(L / K) m))).ResidueField :=
      algebraOfBase (MulAction.stabilizer Gal(L / K) m) m
    Function.Bijective (algebraMap
      (IsLocalRing.maximalIdeal A).ResidueField
      (m.under
        (FixedPoints.subalgebra A (integralClosure A L)
          (MulAction.stabilizer Gal(L / K) m))).ResidueField) := sorry

-- Proof strategy: identify the decomposition-fixed subalgebra as the integral closure in the
-- decomposition fixed field, then apply the decomposition-field residue theorem: the canonical
-- base residue map has trivial extension degree.  Rewrite that map as the algebra map of
-- `algebraOfBase` via `Ideal.ResidueField.algebraMap_algebraOfLiesOver`.

end integralClosure.FixedPoints.ResidueField
