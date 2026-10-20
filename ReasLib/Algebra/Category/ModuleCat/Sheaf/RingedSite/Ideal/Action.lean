/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower
import Mathlib.Tactic.CrossRefAttribute

/-!
# Actions of ideal sheaves

This file owns the action of an ideal sheaf, and of each of its tensor powers, on module
sheaves over an arbitrary commutative ringed site.  The maps are natural in the module, so
constructions that only use ideal multiplication do not need to import internal Homs or kernels.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.IdealSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf J CommRingCat.{w}}

/-- The canonical action `(I : Mod(O)) ⊗ M ⟶ M` induced by the inclusion of an ideal
sheaf into the structure module. -/
@[stacks 0GT5 "ideal-sheaf action"]
noncomputable def action
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory.{u, v, w, w} J O) :
    (tensorObj (I : ringedSiteModuleCategory J O) M :
      ringedSiteModuleCategory J O) ⟶ M :=
  (I.arrow ▷ M) ≫
    ((unitIsoTensorUnit (J := J) (𝒪 := O) ▷ᵢ M) ≪≫ λ_ M).hom

/-- The condition that the uncurried ideal-sheaf action `I ⊗ M ⟶ M` is monomorphic. -/
@[stacks 0GT5 "monomorphic ideal-sheaf action"]
abbrev IsActionMono
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory.{u, v, w, w} J O) : Prop :=
  Mono (action I M)

/-- Naturality of the ideal-sheaf action in the module variable. -/
@[reassoc]
theorem action_naturality
    (I : Subobject (unitModule J O))
    {M N : ringedSiteModuleCategory.{u, v, w, w} J O} (f : M ⟶ N) :
    (tensorLeft (I : ringedSiteModuleCategory J O)).map f ≫ action I N =
      action I M ≫ f := sorry

/-- The action of an ideal sheaf, naturally in the module being acted on. -/
@[stacks 0GT5 "ideal-sheaf action natural transformation"]
noncomputable def actionNat
    (I : Subobject (unitModule J O)) :
    tensorLeft (I : ringedSiteModuleCategory J O) ⟶ 𝟭 _ where
  app M := action I M
  naturality _ _ f := action_naturality I f

/-- The component of `actionNat I` at a module sheaf is `action I M`. -/
@[simp]
theorem actionNat_app
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory.{u, v, w, w} J O) :
    (actionNat I).app M = action I M := sorry

/-- The action of the `n`th tensor power of an ideal sheaf on a module sheaf.  Degree zero is
the structure-module action, and the successor step first applies the preceding power and then
the ideal action. -/
@[stacks 0GT5 "ideal-power action"]
noncomputable def powerAction
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory.{u, v, w, w} J O) :
    (n : ℕ) →
      (tensorObj
        (TensorPower.sheaf O (I : ringedSiteModuleCategory J O) n) M :
          ringedSiteModuleCategory J O) ⟶ M
  | 0 =>
      ((unitIsoTensorUnit (J := J) (𝒪 := O) ▷ᵢ M) ≪≫ λ_ M).hom
  | n + 1 =>
      (α_ (I : ringedSiteModuleCategory J O)
        (TensorPower.sheaf O (I : ringedSiteModuleCategory J O) n) M).hom ≫
        ((I : ringedSiteModuleCategory J O) ◁ powerAction I M n) ≫
        action I M

/-- The zeroth tensor-power action is the canonical structure-module action. -/
theorem powerAction_zero
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory.{u, v, w, w} J O) :
    powerAction I M 0 =
      ((unitIsoTensorUnit (J := J) (𝒪 := O) ▷ᵢ M) ≪≫ λ_ M).hom := sorry

/-- The successor tensor-power action is obtained by reassociating and applying one more ideal
action. -/
theorem powerAction_succ
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory.{u, v, w, w} J O) (n : ℕ) :
    powerAction I M (n + 1) =
      (α_ (I : ringedSiteModuleCategory J O)
        (TensorPower.sheaf O (I : ringedSiteModuleCategory J O) n) M).hom ≫
        ((I : ringedSiteModuleCategory J O) ◁ powerAction I M n) ≫
        action I M := sorry

/-- The first tensor-power action agrees with the ideal action after the canonical
`I^⊗1 ≅ I` comparison. -/
theorem powerAction_one
    (I : Subobject (unitModule J O))
    (M : ringedSiteModuleCategory.{u, v, w, w} J O) :
    powerAction I M 1 =
      ((TensorPower.oneIso O (I : ringedSiteModuleCategory J O)).hom ▷ M) ≫
        action I M := sorry

/-- Naturality of the action of an ideal tensor power in the module variable. -/
@[reassoc]
theorem powerAction_naturality
    (I : Subobject (unitModule J O)) (n : ℕ)
    {M N : ringedSiteModuleCategory.{u, v, w, w} J O} (f : M ⟶ N) :
    (tensorLeft (TensorPower.sheaf O
        (I : ringedSiteModuleCategory J O) n)).map f ≫ powerAction I N n =
      powerAction I M n ≫ f := sorry

/-- The action of the `n`th tensor power of an ideal sheaf, naturally in the module. -/
@[stacks 0GT5 "ideal-power action natural transformation"]
noncomputable def powerActionNat
    (I : Subobject (unitModule J O)) (n : ℕ) :
    tensorLeft (TensorPower.sheaf O
      (I : ringedSiteModuleCategory J O) n) ⟶ 𝟭 _ where
  app M := powerAction I M n
  naturality _ _ f := powerAction_naturality I n f

/-- The component of `powerActionNat I n` at `M` is `powerAction I M n`. -/
@[simp]
theorem powerActionNat_app
    (I : Subobject (unitModule J O)) (n : ℕ)
    (M : ringedSiteModuleCategory.{u, v, w, w} J O) :
    (powerActionNat I n).app M = powerAction I M n := sorry

end SheafOfModules.RingedSite.IdealSheaf
