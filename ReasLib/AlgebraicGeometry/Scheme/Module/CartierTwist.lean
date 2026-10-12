/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.InvertiblePower.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Action
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Quotient.Module
public import Mathlib.CategoryTheory.Subobject.FactorThru

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open SheafOfModules.RingedSite.IdealSheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.CartierTwist

variable {X : Scheme.{u}} (J : X.IdealSheafData) [Scheme.Modules.Invertible J.toModule]

/-- The positive integral tensor power of an invertible ideal sheaf. -/
abbrev positive (c : ℕ) : X.Modules := Scheme.Modules.tensorPowerInt J.toModule (c : ℤ)

/-- The negative integral tensor power of an invertible ideal sheaf. -/
abbrev negative (c : ℕ) : X.Modules := Scheme.Modules.tensorPowerInt J.toModule (-(c : ℤ))

/-- The action of the positive tensor power induced by the ideal inclusion. -/
def action (F : X.Modules) (c : ℕ) : positive J c ⊗ F ⟶ F :=
  ((RingedSpace.InvertiblePower.natIso J.toModule c).inv ▷ F) ≫
    SheafOfModules.RingedSite.IdealSheaf.powerAction J.toSubobject F c

/-- The action of the ordinary `c`-th ideal power on a module. -/
def idealPowerAction (F : X.Modules) (c : ℕ) : (J ^ c).toModule ⊗ F ⟶ F :=
  SheafOfModules.RingedSite.IdealSheaf.action (J ^ c).toSubobject F

/-- Multiplication of the positive tensor power into the structure module. -/
def multiplicationToStructure (c : ℕ) : positive J c ⟶
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  (ρ_ (positive J c)).inv ≫
    (positive J c ◁ (RingedSpace.unitIsoTensorUnit X.toRingedSpace).inv) ≫
    action J (SheafOfModules.unit X.ringCatSheaf) c

/-- The multiplication morphism factors through the ordinary ideal power. -/
theorem multiplication_factors (c : ℕ) :
    (J ^ c).toSubobject.Factors (multiplicationToStructure J c) := sorry

/-- The canonical factorization of multiplication through the ideal power. -/
def multiplicationToPower (c : ℕ) : positive J c ⟶ (J ^ c).toModule :=
  (J ^ c).toSubobject.factorThru (multiplicationToStructure J c) (multiplication_factors J c)

/-- The factorization through the ideal power composes to multiplication. -/
theorem multiplicationToPower_spec (c : ℕ) :
    multiplicationToPower J c ≫ (J ^ c).toSubobject.arrow = multiplicationToStructure J c := by
  exact Subobject.factorThru_arrow _ _ _

/-- The multiplication comparison is an isomorphism for an invertible ideal sheaf. -/
instance multiplicationToPower_isIso (c : ℕ) : IsIso (multiplicationToPower J c) := sorry

/-- The tensor-power action factors through the ordinary ideal-power action. -/
theorem action_factors (F : X.Modules) (c : ℕ) :
    (multiplicationToPower J c ▷ F) ≫ idealPowerAction J F c = action J F c := sorry

/-- Vanishing of the tensor-power action is equivalent to vanishing of the ideal-power action. -/
theorem action_eq_zero_iff_idealPowerAction (F : X.Modules) (c : ℕ) :
    action J F c = 0 ↔ idealPowerAction J F c = 0 := by
  rw [← action_factors J F c]
  constructor
  · intro h
    apply (cancel_epi (multiplicationToPower J c ▷ F)).mp
    exact h.trans (comp_zero).symm
  · intro h
    rw [h]
    exact comp_zero

/-- The evaluation isomorphism between positive and negative integral powers. -/
def inverseEvaluation (c : ℕ) : positive J c ⊗ negative J c ≅ 𝟙_ X.Modules :=
  RingedSpace.InvertiblePower.addIso J.toModule (c : ℤ) (-(c : ℤ)) ≪≫
    RingedSpace.InvertiblePower.indexIso J.toModule (add_neg_cancel (c : ℤ)) ≪≫
    RingedSpace.InvertiblePower.zeroIso J.toModule ≪≫
    RingedSpace.unitIsoTensorUnit X.toRingedSpace

/-- The normalized exact pairing of the positive and negative tensor powers. -/
@[implicit_reducible]
def pairing (c : ℕ) : ExactPairing (positive J c) (negative J c) :=
  MonoidalClosed.RightInverse.pairing _ _ (inverseEvaluation J c)

/-- The tensor adjunction between the positive action and negative twist maps. -/
def transpose (F : X.Modules) (c : ℕ) :
    (positive J c ⊗ F ⟶ F) ≃ (F ⟶ F ⊗ negative J c) := by
  -- Local instance justification (proof-local temporary data): the Hom equivalence uses the normalized pairing of these specified powers.
  letI := pairing J c
  exact (Iso.homCongr (β_ (positive J c) F) (Iso.refl F)).trans
    (tensorRightHomEquiv F (positive J c) (negative J c) F)

/-- The canonical map from a module to its negative Cartier twist. -/
def map (F : X.Modules) (c : ℕ) : F ⟶ F ⊗ negative J c :=
  transpose J F c (action J F c)

/-- The tensor adjunction sends the zero morphism to the zero morphism. -/
theorem transpose_zero (F : X.Modules) (c : ℕ) : transpose J F c 0 = 0 := by
  dsimp [transpose, tensorRightHomEquiv, Iso.homCongr]
  simp

/-- The canonical negative-twist map vanishes exactly when the tensor action does. -/
theorem map_eq_zero_iff_action (F : X.Modules) (c : ℕ) :
    map J F c = 0 ↔ action J F c = 0 := by
  rw [map, ← transpose_zero J F c]
  exact (transpose J F c).injective.eq_iff

/-- A module is annihilated by an ideal power exactly when its ideal action vanishes. -/
theorem annihilated_iff_action (F : X.Modules) (c : ℕ) :
    IsAnnihilated (J ^ c).toSubobject F ↔ idealPowerAction J F c = 0 := sorry

/-- A module is annihilated by an ideal power exactly when its canonical twist map vanishes. -/
theorem annihilated_iff_map (F : X.Modules) (c : ℕ) :
    IsAnnihilated (J ^ c).toSubobject F ↔ map J F c = 0 := by
  rw [map_eq_zero_iff_action, action_eq_zero_iff_idealPowerAction]
  exact annihilated_iff_action J F c

end AlgebraicGeometry.Scheme.Modules.CartierTwist
