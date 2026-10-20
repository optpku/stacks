/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Picard.Cohomology

/-!
# The Picard group as first cohomology of units

This file bundles the canonical Picard cohomology-class map as an additive
equivalence.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.PicardGroup

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (A : Sheaf J CommRingCat.{max u v})
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{max u v})]
variable [A.IsLocallyRinged]

/-- The underlying inverse function to the Picard cohomology-class map.

Its computational content is `Function.invFun`; the inverse and additivity
laws below isolate the proof-valued classification input. -/
noncomputable def cohomologyInverseFunction :
    (CategoryTheory.Sheaf.unitsAddSheaf A).H 1 → PicardGroup J A :=
  Function.invFun (cohomologyClass A)

/-- The inverse function sends zero to the neutral Picard class. -/
theorem cohomologyInverseFunction_zero : cohomologyInverseFunction A 0 = 0 := sorry

/-- The inverse function is additive. -/
theorem cohomologyInverseFunction_add
    (x y : (CategoryTheory.Sheaf.unitsAddSheaf A).H 1) :
    cohomologyInverseFunction A (x + y) =
      cohomologyInverseFunction A x + cohomologyInverseFunction A y := sorry

/-- Applying the inverse function after `cohomologyClass` recovers a Picard
class. -/
theorem cohomologyInverseFunction_cohomologyClass (x : PicardGroup J A) :
    cohomologyInverseFunction A (cohomologyClass A x) = x := sorry

/-- Applying `cohomologyClass` after its inverse function recovers the
cohomology class. -/
theorem cohomologyClass_cohomologyInverseFunction
    (x : (CategoryTheory.Sheaf.unitsAddSheaf A).H 1) :
    cohomologyClass A (cohomologyInverseFunction A x) = x := sorry

/-- The inverse additive homomorphism from first units cohomology to the
Picard group. -/
noncomputable def cohomologyInverse :
    (CategoryTheory.Sheaf.unitsAddSheaf A).H 1 →+ PicardGroup J A where
  toFun := cohomologyInverseFunction A
  map_zero' := cohomologyInverseFunction_zero A
  map_add' := cohomologyInverseFunction_add A

/-- The additive equivalence from the Picard group to first cohomology of the
units sheaf. -/
noncomputable def cohomologyEquiv :
    PicardGroup J A ≃+ (CategoryTheory.Sheaf.unitsAddSheaf A).H 1 where
  toFun := cohomologyClass A
  invFun := cohomologyInverseFunction A
  left_inv := cohomologyInverseFunction_cohomologyClass A
  right_inv := cohomologyClass_cohomologyInverseFunction A
  map_add' := (cohomologyClass A).map_add

/-- Applying the inverse comparison after `cohomologyClass` recovers a
Picard class. -/
theorem cohomologyInverse_cohomologyClass (x : PicardGroup J A) :
    cohomologyInverse A (cohomologyClass A x) = x := sorry

/-- Applying `cohomologyClass` after its inverse recovers the cohomology
class. -/
theorem cohomologyClass_cohomologyInverse
    (x : (CategoryTheory.Sheaf.unitsAddSheaf A).H 1) :
    cohomologyClass A (cohomologyInverse A x) = x := sorry

/-- The forward map of `cohomologyEquiv` is the canonical Picard cohomology
class map. -/
theorem cohomologyEquiv_apply (x : PicardGroup J A) :
    cohomologyEquiv A x = cohomologyClass A x := sorry

end SheafOfModules.RingedSite.PicardGroup
