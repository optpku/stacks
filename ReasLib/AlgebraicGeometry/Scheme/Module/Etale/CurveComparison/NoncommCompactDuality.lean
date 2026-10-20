/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommCompactCharacters
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

@[expose] public section
open CategoryTheory Opposite
noncomputable section
universe u

namespace NoncommCompactDuality
variable (R : Type u) [Ring R] [Finite R]

/-- Only continuous characters of a compact module are admitted. -/
def characters (M : NoncommCompactModule R) :
    Submodule Rᵐᵒᵖ (ActualOppositeCharacter.Carrier M.toModule) where
  carrier := {χ | Continuous (NoncommCompactCharacters.coordinates R M.toModule χ)}
  zero_mem' := by sorry
  add_mem' := by sorry
  smul_mem' := by sorry

/-- The actual opposite-coefficient module of continuous characters. -/
def characterModule (M : NoncommCompactModule R) : ModuleCat.{u} Rᵐᵒᵖ :=
  ModuleCat.of Rᵐᵒᵖ (characters R M)

/-- Continuous character precomposition, restricted to the actual submodules. -/
def characterMap {M N : NoncommCompactModule R} (f : M ⟶ N) :
    characterModule R N ⟶ characterModule R M :=
  ModuleCat.ofHom (LinearMap.codRestrict (characters R M)
    ((ActualOppositeCharacter.map R M.toModule
      (show M.toModule →L[R] N.toModule from f).toLinearMap).domRestrict (characters R N))
    (by sorry))

/-- Continuous character duality is contravariant and reverses scalar handedness. -/
def continuousFunctor : (NoncommCompactModule R)ᵒᵖ ⥤ ModuleCat.{u} Rᵐᵒᵖ where
  obj M := characterModule R M.unop
  map f := characterMap R f.unop
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- Remove the DOUBLE opposite using its actual canonical ring homomorphism. -/
def inverseDiscrete (M : NoncommCompactModule Rᵐᵒᵖ) : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars (RingEquiv.opOp R).toRingHom).obj (characterModule Rᵐᵒᵖ M)

/-- The inverse functor uses continuous characters and double-opposite scalar restriction. -/
def inverse : NoncommCompactModule Rᵐᵒᵖ ⥤ (ModuleCat.{u} R)ᵒᵖ :=
  (continuousFunctor Rᵐᵒᵖ ⋙ ModuleCat.restrictScalars (RingEquiv.opOp R).toRingHom).rightOp

/-- Evaluate a discrete vector on actual right characters. -/
def discreteEvaluation (M : ModuleCat.{u} R) :
    M →ₗ[R] inverseDiscrete R (NoncommCompactCharacters.dual R M) where
  toFun m := ⟨(show ActualOppositeCharacter.Carrier
      (NoncommCompactCharacters.dual R M).toModule from
    { toFun := fun χ ↦ (show ActualOppositeCharacter.Carrier M from χ) m
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }), by sorry⟩
  map_add' := by sorry
  map_smul' := by sorry

/-- Discrete/compact finite-exponent Pontryagin duality for the specified evaluation. -/
theorem discreteEvaluation_bijective (M : ModuleCat.{u} R) :
    Function.Bijective (discreteEvaluation R M) := by sorry

/-- The unit is constructed from evaluation, not an arbitrary isomorphism. -/
def discreteEvaluationIso (M : ModuleCat.{u} R) :
    M ≅ inverseDiscrete R (NoncommCompactCharacters.dual R M) :=
  (LinearEquiv.ofBijective (discreteEvaluation R M)
    (discreteEvaluation_bijective R M)).toModuleIso

/-- Compact evaluation tests only continuous characters. -/
def compactEvaluation (M : NoncommCompactModule Rᵐᵒᵖ) :
    M.toModule →ₗ[Rᵐᵒᵖ] (NoncommCompactCharacters.dual R (inverseDiscrete R M)).toModule where
  toFun m :=
    { toFun := fun χ ↦ χ.val m
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  map_add' := by sorry
  map_smul' := by sorry

/-- Continuity is checked in every finite evaluation coordinate. -/
theorem compactEvaluation_continuous (M : NoncommCompactModule Rᵐᵒᵖ) :
    Continuous (compactEvaluation R M) := by sorry

/-- This is continuous biduality, not the false unrestricted algebraic bidual statement. -/
theorem compactEvaluation_bijective (M : NoncommCompactModule Rᵐᵒᵖ) :
    Function.Bijective (compactEvaluation R M) := by sorry

/-- The specified evaluation determines the inverse function. -/
def compactEvaluationEquiv (M : NoncommCompactModule Rᵐᵒᵖ) :=
  LinearEquiv.ofBijective (compactEvaluation R M) (compactEvaluation_bijective R M)

/-- Compact-to-Hausdorff bijectivity makes the actual evaluation inverse continuous. -/
theorem compactEvaluation_inverse_continuous (M : NoncommCompactModule Rᵐᵒᵖ) :
    Continuous (compactEvaluationEquiv R M).symm := by sorry

/-- Actual compact evaluation and its continuous inverse, retaining opposite scalars. -/
def compactEvaluationIso (M : NoncommCompactModule Rᵐᵒᵖ) :
    M ≅ NoncommCompactCharacters.dual R (inverseDiscrete R M) where
  hom := { toLinearMap := compactEvaluation R M
           cont := compactEvaluation_continuous R M }
  inv := { toLinearMap := (compactEvaluationEquiv R M).symm.toLinearMap
           cont := compactEvaluation_inverse_continuous R M }
  hom_inv_id := by sorry
  inv_hom_id := by sorry

/-- Noncommutative compact/discrete anti-equivalence with the specified evaluation
unit and counit. Left R-modules correspond to compact RIGHT R-modules. -/
def equivalence : (ModuleCat.{u} R)ᵒᵖ ≌ NoncommCompactModule Rᵐᵒᵖ where
  functor := NoncommCompactCharacters.functor R
  inverse := inverse R
  unitIso := NatIso.ofComponents (fun M ↦ (discreteEvaluationIso R M.unop).symm.op) (by sorry)
  counitIso := NatIso.ofComponents (fun M ↦ (compactEvaluationIso R M).symm) (by sorry)
  functor_unitIso_comp := by sorry

end NoncommCompactDuality
