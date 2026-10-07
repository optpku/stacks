module

public import ReasLib.Algebra.Category.CommRingCat.IdealPower
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedExtension.ConeModel
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived Towers over Ideal-Power Quotients

This file specializes derived module towers to the canonical inverse system
`A ⧸ I ^ (n + 1)` and supplies the canonical fixed-base tower over `A`.
@stack 09AU
@stack 09AV
@stack 09AW
@stack 0CQF
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat

variable {A : Type u} [CommRing A]

/-- A compatible tower of derived modules over the quotients `A ⧸ I ^ (n + 1)`. -/
@[stacks 0CQF "derived module tower over ideal-power quotients"]
abbrev IdealPowerTower (I : Ideal A) :=
  DerivedTower (CommRingCat.IdealPower.Positive.system I)

namespace IdealPowerTower

/-- An explicit derived extension model from `A` to the `n`th positive ideal-power quotient. -/
@[stacks 09AV "derived extension to an ideal-power quotient",
  stacks 09AW "derived extension to an ideal-power quotient",
  stacks 09AU "derived extension to an ideal-power quotient"]
abbrev Extension (I : Ideal A) (n : ℕ) :=
  DerivedExtension ((CommRingCat.IdealPower.Positive.cone I).stageMap n).hom

/-- Explicit derived extension models along all stages and transitions of the positive
ideal-power quotient system. -/
@[stacks 0CQF "explicit derived extension model for an ideal-power tower"]
abbrev ExtensionModel (I : Ideal A) :=
  DerivedExtension.ConeModel (CommRingCat.IdealPower.Positive.cone I)

/-- Restrict every stage of an ideal-power derived tower along `A ⟶ A ⧸ I ^ (n + 1)`. -/
@[stacks 0CQF "ideal-power derived tower over the base ring"]
noncomputable abbrev toBase {I : Ideal A} (T : IdealPowerTower I) :
    SequentialInverseSystem (DerivedCategory (ModuleCat.{u, u} A)) :=
  T.restrict (CommRingCat.IdealPower.Positive.cone I)

/-- Evaluation of the fixed-base ideal-power tower at stage `n`. -/
@[simp]
theorem toBase_obj {I : Ideal A} (T : IdealPowerTower I) (n : ℕ) :
    T.toBase.obj (Opposite.op n) =
      (derivedRestrictionOfScalars (Ideal.Quotient.mk (I ^ (n + 1)))).obj (T.obj n) := sorry

/-- The transition of the fixed-base ideal-power tower is the canonical restricted transition. -/
@[simp]
theorem toBase_stepMap {I : Ideal A} (T : IdealPowerTower I) (n : ℕ) :
    T.toBase.stepMap n =
      T.restrictStep (CommRingCat.IdealPower.Positive.cone I) n := sorry

end IdealPowerTower

end CategoryTheory.ModuleCat
