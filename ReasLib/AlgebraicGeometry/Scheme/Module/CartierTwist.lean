/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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

/-- Multiplication by `c` ideal factors is zero in the quotient by `J ^ c`. -/
private theorem multiplication_comp_quotient (c : ℕ) :
    multiplicationToStructure J c ≫ SheafOfModules.unitToPushforwardObjUnit
      (RingedSpace.Hom.toRingCatSheafHom (J ^ c).subschemeι.toShHom) = 0 := sorry

/-- The multiplication morphism factors through the ordinary ideal power. -/
theorem multiplication_factors (c : ℕ) :
    (J ^ c).toSubobject.Factors (multiplicationToStructure J c) := by
  exact kernelSubobject_factors _ _ (multiplication_comp_quotient J c)

/-- The canonical factorization of multiplication through the ideal power, constructed by the
kernel universal property of the defining quotient map. -/
def multiplicationToPower (c : ℕ) : positive J c ⟶ (J ^ c).toModule :=
  kernel.lift _ (multiplicationToStructure J c) (by exact multiplication_comp_quotient J c) ≫
    (kernelSubobjectIso _).inv

/-- The factorization through the ideal power composes to multiplication. -/
theorem multiplicationToPower_spec (c : ℕ) :
    multiplicationToPower J c ≫ (J ^ c).toSubobject.arrow = multiplicationToStructure J c := by
  change (kernel.lift _ _ _ ≫ (kernelSubobjectIso _).inv) ≫
    (kernelSubobject _).arrow = _
  rw [Category.assoc, kernelSubobject_arrow', kernel.lift_ι]

/-- The multiplication comparison is an isomorphism for an invertible ideal sheaf. -/
instance multiplicationToPower_isIso (c : ℕ) : IsIso (multiplicationToPower J c) := sorry

set_option backward.isDefEq.respectTransparency false in
omit [Scheme.Modules.Invertible J.toModule] in
private theorem powerAction_tensorRight (M N : X.Modules) (c : ℕ) :
    (α_ (RingedSpace.TensorPower.sheaf J.toModule c) M N).hom ≫
      powerAction J.toSubobject (M ⊗ N) c = powerAction J.toSubobject M c ▷ N := by
  induction c with
  | zero =>
    dsimp only [powerAction]
    simp only [Iso.trans_hom, whiskerRightIso]
    monoidal
  | succ c ih =>
    have h : powerAction J.toSubobject (M ⊗ N) c =
        (α_ (RingedSpace.TensorPower.sheaf J.toModule c) M N).inv ≫
          (powerAction J.toSubobject M c ▷ N) := by
      rw [← ih, Iso.inv_hom_id_assoc]
    dsimp only [powerAction]
    rw [h]
    dsimp only [SheafOfModules.RingedSite.IdealSheaf.action]
    simp only [Iso.trans_hom, whiskerRightIso, comp_whiskerRight]
    monoidal

set_option backward.isDefEq.respectTransparency false in
omit [Scheme.Modules.Invertible J.toModule] in
private theorem powerAction_via_unit (F : X.Modules) (c : ℕ) :
    (((ρ_ (RingedSpace.TensorPower.sheaf J.toModule c)).inv ≫
      (RingedSpace.TensorPower.sheaf J.toModule c ◁
        (RingedSpace.unitIsoTensorUnit X.toRingedSpace).inv) ≫
      powerAction J.toSubobject (SheafOfModules.unit X.ringCatSheaf) c) ▷ F) ≫
      ((RingedSpace.unitIsoTensorUnit X.toRingedSpace).hom ▷ F) ≫
      (λ_ F).hom = powerAction J.toSubobject F c := by
  let P := RingedSpace.TensorPower.sheaf J.toModule c
  let U : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let e : U ≅ 𝟙_ X.Modules := RingedSpace.unitIsoTensorUnit X.toRingedSpace
  let r : U ⊗ F ≅ F := (e ▷ᵢ F) ≪≫ λ_ F
  have ht := powerAction_tensorRight J U F c
  have hn : P ◁ r.hom ≫ powerAction J.toSubobject F c =
      powerAction J.toSubobject (U ⊗ F) c ≫ r.hom :=
    powerAction_naturality J.toSubobject c r.hom
  change (((ρ_ P).inv ≫ (P ◁ e.inv) ≫ powerAction J.toSubobject U c) ▷ F) ≫
    (e.hom ▷ F) ≫ (λ_ F).hom = _
  calc
    _ = ((ρ_ P).inv ▷ F) ≫ ((P ◁ e.inv) ▷ F) ≫
        (α_ P U F).hom ≫ powerAction J.toSubobject (U ⊗ F) c ≫ r.hom := by
      rw [← Category.assoc (α_ P U F).hom, ht]
      dsimp only [r]
      simp only [comp_whiskerRight, Category.assoc, Iso.trans_hom, whiskerRightIso]
    _ = ((ρ_ P).inv ▷ F) ≫ ((P ◁ e.inv) ▷ F) ≫
        (α_ P U F).hom ≫ (P ◁ r.hom) ≫ powerAction J.toSubobject F c := by
      rw [← hn]
    _ = _ := by
      dsimp only [r]
      simp only [Iso.trans_hom, whiskerRightIso]
      monoidal
      simp only [whiskerLeftIso_refl, whiskerRightIso_refl, Iso.trans_refl, Iso.refl_trans,
        Iso.trans_hom, whiskerRightIso_hom, Iso.symm_hom, triangle_assoc_comp_right_inv,
        Iso.symm_self_id, Iso.refl_hom, whiskerLeftIso_hom, Category.comp_id, Category.assoc,
        Category.id_comp, cancelIso, whiskerLeft_inv_hom_assoc]
      exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
private theorem action_via_multiplication (F : X.Modules) (c : ℕ) :
    ((multiplicationToStructure J c ≫
      (RingedSpace.unitIsoTensorUnit X.toRingedSpace).hom) ▷ F) ≫
      (λ_ F).hom = action J F c := by
  dsimp only [multiplicationToStructure, action]
  simp only [Category.assoc]
  rw [whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc]
  rw [← powerAction_via_unit J F c]
  simp only [comp_whiskerRight, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The tensor-power action factors through the ordinary ideal-power action. -/
theorem action_factors (F : X.Modules) (c : ℕ) :
    (multiplicationToPower J c ▷ F) ≫ idealPowerAction J F c = action J F c := by
  calc
    _ = ((multiplicationToPower J c ≫ (J ^ c).toSubobject.arrow ≫
        (RingedSpace.unitIsoTensorUnit X.toRingedSpace).hom) ▷ F) ≫
        (λ_ F).hom := by
      dsimp only [idealPowerAction, SheafOfModules.RingedSite.IdealSheaf.action]
      simp only [Iso.trans_hom, whiskerRightIso, comp_whiskerRight, Category.assoc]
    _ = ((multiplicationToStructure J c ≫
        (RingedSpace.unitIsoTensorUnit X.toRingedSpace).hom) ▷ F) ≫
        (λ_ F).hom := by
      rw [← Category.assoc, multiplicationToPower_spec]
    _ = _ := action_via_multiplication J F c

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
