/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Composition

/-!
# Associativity of cartesian based functors

Composition of cartesian functors over a common base has the ordinary identity-component
associator, with independent universes for each total category.
-/

@[expose] public section

universe u v u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

namespace CategoryTheory.CartesianBasedFunctor

variable {C : Type u} [Category.{v} C]
variable {S₁ : Type u₁} {S₂ : Type u₂} {S₃ : Type u₃} {S₄ : Type u₄}
variable [Category.{v₁} S₁] [Category.{v₂} S₂] [Category.{v₃} S₃] [Category.{v₄} S₄]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C} {p₃ : S₃ ⥤ C} {p₄ : S₄ ⥤ C}

/-- The identity-component associator for three cartesian functors over a common base. -/
def associator (F : CartesianBasedFunctor p₁ p₂) (G : CartesianBasedFunctor p₂ p₃)
    (H : CartesianBasedFunctor p₃ p₄) : (F.comp G).comp H ≅ F.comp (G.comp H) :=
  ObjectProperty.isoMk _ (BasedNatIso.mkNatIso
    (F := ((F.comp G).comp H).toBasedFunctor)
    (G := (F.comp (G.comp H)).toBasedFunctor)
    (Functor.associator F.toFunctor G.toFunctor H.toFunctor)
    (fun x ↦ IsHomLift.id
      (BasedFunctor.w_obj ((F.comp G).comp H).toBasedFunctor x)))

/-- The forward component of the cartesian associator is the identity. -/
@[simp]
theorem associator_hom_app (F : CartesianBasedFunctor p₁ p₂)
    (G : CartesianBasedFunctor p₂ p₃) (H : CartesianBasedFunctor p₃ p₄) (x : S₁) :
    (associator F G H).hom.hom.toNatTrans.app x =
      𝟙 (H.toFunctor.obj (G.toFunctor.obj (F.toFunctor.obj x))) := rfl

/-- The inverse component of the cartesian associator is the identity. -/
@[simp]
theorem associator_inv_app (F : CartesianBasedFunctor p₁ p₂)
    (G : CartesianBasedFunctor p₂ p₃) (H : CartesianBasedFunctor p₃ p₄) (x : S₁) :
    (associator F G H).inv.hom.toNatTrans.app x =
      𝟙 (H.toFunctor.obj (G.toFunctor.obj (F.toFunctor.obj x))) := rfl

end CategoryTheory.CartesianBasedFunctor
