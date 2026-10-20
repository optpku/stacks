module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactModules
public import Mathlib.CategoryTheory.Opposites

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u

namespace CompactModule

variable (Λ : Type u) [CommRing Λ] [Finite Λ]

/-- Continuous characters of an actual compact module. Values lie in the
finite annihilator; an arbitrary algebraic character is not admitted. -/
def characters (M : CompactModule Λ) : Submodule Λ (CharacterModule M.toModule) where
  carrier := {χ | Continuous (CompactCharacters.evaluationCoordinates Λ M.toModule χ)}
  zero_mem' := by sorry
  add_mem' := by sorry
  smul_mem' := by sorry

def characterModule (M : CompactModule Λ) : ModuleCat.{u} Λ :=
  ModuleCat.of Λ (characters Λ M)

/-- Actual precomposition, restricted to continuous characters. -/
def characterMap {M N : CompactModule Λ} (f : M ⟶ N) :
    characterModule Λ N ⟶ characterModule Λ M :=
  ModuleCat.ofHom
    (LinearMap.codRestrict (characters Λ M)
      ((CharacterModule.dual (linear Λ f)).domRestrict (characters Λ N)) (by sorry))

def continuousCharacterFunctor : (CompactModule Λ)ᵒᵖ ⥤ ModuleCat.{u} Λ where
  obj M := characterModule Λ M.unop
  map f := characterMap Λ f.unop
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- The discrete evaluation map sends m to the continuous character χ ↦ χ(m). -/
def discreteEvaluation (M : ModuleCat.{u} Λ) :
    M →ₗ[Λ] characterModule Λ (ofCharacter Λ M) :=
  LinearMap.codRestrict (characters Λ (ofCharacter Λ M))
    (CharacterModule.evalLinear Λ) (by sorry)

theorem discreteEvaluation_bijective (M : ModuleCat.{u} Λ) :
    Function.Bijective (discreteEvaluation Λ M) := by sorry

def discreteEvaluationIso (M : ModuleCat.{u} Λ) :
    M ≅ characterModule Λ (ofCharacter Λ M) :=
  (LinearEquiv.ofBijective (discreteEvaluation Λ M)
    (discreteEvaluation_bijective Λ M)).toModuleIso

/-- Compact evaluation tests only continuous characters. -/
def compactEvaluation (M : CompactModule Λ) :
    M.toModule →ₗ[Λ] (ofCharacter Λ (characterModule Λ M)).toModule where
  toFun m :=
    { toFun := fun χ ↦ χ.val m
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  map_add' := by sorry
  map_smul' := by sorry

theorem compactEvaluation_continuous (M : CompactModule Λ) :
    Continuous (compactEvaluation Λ M) := by sorry

theorem compactEvaluation_bijective (M : CompactModule Λ) :
    Function.Bijective (compactEvaluation Λ M) := by sorry

def compactEvaluationEquiv (M : CompactModule Λ) :
    M.toModule ≃ₗ[Λ] (ofCharacter Λ (characterModule Λ M)).toModule :=
  LinearEquiv.ofBijective (compactEvaluation Λ M) (compactEvaluation_bijective Λ M)

/-- The inverse of this specified continuous bijection is continuous by
compactness and Hausdorffness. -/
theorem compactEvaluation_inverse_continuous (M : CompactModule Λ) :
    Continuous (compactEvaluationEquiv Λ M).symm := by sorry

def compactEvaluationIso (M : CompactModule Λ) :
    M ≅ ofCharacter Λ (characterModule Λ M) where
  hom :=
    { toLinearMap := compactEvaluation Λ M
      cont := compactEvaluation_continuous Λ M }
  inv :=
    { toLinearMap := (compactEvaluationEquiv Λ M).symm.toLinearMap
      cont := compactEvaluation_inverse_continuous Λ M }
  hom_inv_id := by
    apply ContinuousLinearMap.ext
    intro x
    exact (compactEvaluationEquiv Λ M).left_inv x
  inv_hom_id := by
    apply ContinuousLinearMap.ext
    intro x
    exact (compactEvaluationEquiv Λ M).right_inv x

/-- Contravariant continuous character duality, with evaluation unit/counit. -/
def characterEquivalence : (ModuleCat.{u} Λ)ᵒᵖ ≌ CompactModule Λ where
  functor := characterFunctor Λ
  inverse := (continuousCharacterFunctor Λ).rightOp
  unitIso := NatIso.ofComponents (fun M ↦ (discreteEvaluationIso Λ M.unop).symm.op) (by sorry)
  counitIso := NatIso.ofComponents (fun M ↦ (compactEvaluationIso Λ M).symm) (by sorry)
  functor_unitIso_comp := by sorry

end CompactModule
