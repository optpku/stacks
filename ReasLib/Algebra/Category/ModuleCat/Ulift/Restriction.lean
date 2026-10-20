/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Universe lift and restriction of scalars -/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace ModuleCat

/-- Universe-lifted restriction of scalars commutes with `uliftFunctor`. -/
def uliftRestrictScalarsIso {A B : Type u} [CommRing A] [CommRing B] (σ : A →+* B) :
    ModuleCat.restrictScalars.{u} σ ⋙ ModuleCat.uliftFunctor.{u + 1, u} A ≅
      ModuleCat.uliftFunctor.{u + 1, u} B ⋙ ModuleCat.restrictScalars.{u + 1} σ :=
  NatIso.ofComponents
    (fun M ↦
      { hom := ConcreteCategory.ofHom
          { toFun := fun x ↦ x
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun _ _ ↦ rfl }
        inv := ConcreteCategory.ofHom
          { toFun := fun x ↦ x
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun _ _ ↦ rfl }
        hom_inv_id := by ext x; rfl
        inv_hom_id := by ext x; rfl })
    (fun {X Y} f ↦ sorry)

/-- `uliftRestrictScalarsIso` acts as the identity on the underlying `ULift`
carrier. -/
theorem uliftRestrictScalarsIso_hom_app {A B : Type u} [CommRing A] [CommRing B]
    (σ : A →+* B) (M : ModuleCat.{u} B)
    (x : (ModuleCat.restrictScalars.{u} σ ⋙
        ModuleCat.uliftFunctor.{u + 1, u} A).obj M) :
    (uliftRestrictScalarsIso σ).hom.app M x = x :=
  rfl

end ModuleCat
