/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.EilenbergWatts
public import ReasLib.Algebra.Category.ModuleCat.ProductPower
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.Prod

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

namespace ModuleCat

/-- Restriction of scalars along the factor-swapping automorphism of `ℤ × ℤ`. -/
noncomputable abbrev restrictScalars_prodComm :
    ModuleCat.{u} (ℤ × ℤ) ⥤ ModuleCat.{u} (ℤ × ℤ) :=
  restrictScalars (RingEquiv.prodComm : ℤ × ℤ ≃+* ℤ × ℤ).toRingHom

/-- Additivity of restriction of scalars along the factor-swapping automorphism. -/
noncomputable def restrictScalars_prodComm_additive :
    restrictScalars_prodComm.{u}.Additive := inferInstance

/-- The factor-swapping restriction-of-scalars functor is not linear. -/
theorem not_linear_restrictScalars_prodComm :
    ¬ restrictScalars_prodComm.{u}.Linear (ℤ × ℤ) := sorry

/-- The countable product-power comparison is not invertible over a nontrivial ring. -/
theorem not_isIso_tensorRightComparison_piConst {R : Type u} [CommRing R] [Nontrivial R] :
    ¬ IsIso (tensorRightComparison (piConst R (ULift.{u} ℕ))) := sorry

/-- The countable product-power functor is not tensoring by any module. -/
theorem piConst_not_iso_tensorRight {R : Type u} [CommRing R] [Nontrivial R]
    (N : ModuleCat.{u} R) :
    ¬ Nonempty (piConst R (ULift.{u} ℕ) ≅ tensorRight N) := sorry

end ModuleCat
