module

public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.Basic

/-!
# Endpoint isomorphisms for canonical Hom-presheaves

This module packages conjugation by isomorphisms of the source and target
fiber objects. Its interaction with endpoint actions and the endpoint functor
is recorded separately in `Endpoint.Functoriality`.
-/

@[expose] public section

universe uC vC uP vP

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

namespace Pseudofunctor

variable {C : Type uC} [Category.{vC} C]

/-- Objectwise endpoint conjugation on a canonical Hom-presheaf. -/
def PresheafHom.Congr.appEquiv
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op U))}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) (W : (Over U)ᵒᵖ) :
    (F.presheafHom x₁ y₁).obj W ≃ (F.presheafHom x₂ y₂).obj W :=
  Iso.homCongr
    ((F.map W.unop.hom.op.toLoc).toFunctor.mapIso ex)
    ((F.map W.unop.hom.op.toLoc).toFunctor.mapIso ey)

/-- Endpoint conjugation is natural in the opposite slice object. -/
theorem PresheafHom.Congr.AppEquiv.naturality
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op U))}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) :
    ∀ ⦃W₁ W₂ : (Over U)ᵒᵖ⦄ (α : W₁ ⟶ W₂),
      (F.presheafHom x₁ y₁).map α ≫
          (Equiv.toIso (PresheafHom.Congr.appEquiv F ex ey W₂)).hom =
        (Equiv.toIso (PresheafHom.Congr.appEquiv F ex ey W₁)).hom ≫
          (F.presheafHom x₂ y₂).map α := sorry

/-- Conjugation by isomorphisms of both endpoint objects, as an isomorphism of canonical
Hom-presheaves. -/
def PresheafHom.Congr.iso
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op U))}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) :
    F.presheafHom x₁ y₁ ≅ F.presheafHom x₂ y₂ :=
  NatIso.ofComponents
    (fun W ↦ Equiv.toIso (PresheafHom.Congr.appEquiv F ex ey W))
    (fun {_ _} α ↦ PresheafHom.Congr.AppEquiv.naturality F ex ey α)

/-- The forward component of endpoint conjugation is the objectwise Hom equivalence. -/
@[simp]
theorem PresheafHom.Congr.Iso.Hom.app
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op U))}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) (W : (Over U)ᵒᵖ) :
    (PresheafHom.Congr.iso F ex ey).hom.app W =
      (Equiv.toIso (PresheafHom.Congr.appEquiv F ex ey W)).hom := sorry

/-- The inverse component of endpoint conjugation is the inverse objectwise Hom equivalence. -/
@[simp]
theorem PresheafHom.Congr.Iso.Inv.app
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op U))}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) (W : (Over U)ᵒᵖ) :
    (PresheafHom.Congr.iso F ex ey).inv.app W =
      (Equiv.toIso (PresheafHom.Congr.appEquiv F ex ey W)).inv := sorry

/-- Elementwise computation of the forward endpoint-conjugation map. -/
@[simp]
theorem PresheafHom.Congr.Iso.Hom.appApply
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op U))}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) (W : (Over U)ᵒᵖ)
    (φ : (F.presheafHom x₁ y₁).obj W) :
    (PresheafHom.Congr.iso F ex ey).hom.app W φ =
      Iso.homCongr
        ((F.map W.unop.hom.op.toLoc).toFunctor.mapIso ex)
        ((F.map W.unop.hom.op.toLoc).toFunctor.mapIso ey) φ := sorry

/-- Elementwise computation of the inverse endpoint-conjugation map. -/
@[simp]
theorem PresheafHom.Congr.Iso.Inv.appApply
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op U))}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) (W : (Over U)ᵒᵖ)
    (φ : (F.presheafHom x₂ y₂).obj W) :
    (PresheafHom.Congr.iso F ex ey).inv.app W φ =
      Iso.homCongr
        ((F.map W.unop.hom.op.toLoc).toFunctor.mapIso ex.symm)
        ((F.map W.unop.hom.op.toLoc).toFunctor.mapIso ey.symm) φ := sorry

/-- At the identity slice, the forward endpoint-conjugation map is ordinary conjugation. -/
@[simp]
theorem PresheafHom.Congr.Iso.Hom.identitySlice
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op U))}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) (φ : x₁ ⟶ y₁) :
    (PresheafHom.Congr.iso F ex ey).hom.app (op (Over.mk (𝟙 U)))
        (F.presheafHomObjHomEquiv φ) =
      F.presheafHomObjHomEquiv (ex.inv ≫ φ ≫ ey.hom) := sorry

/-- At the identity slice, the inverse endpoint-conjugation map is inverse conjugation. -/
@[simp]
theorem PresheafHom.Congr.Iso.Inv.identitySlice
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op U))}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) (φ : x₂ ⟶ y₂) :
    (PresheafHom.Congr.iso F ex ey).inv.app (op (Over.mk (𝟙 U)))
        (F.presheafHomObjHomEquiv φ) =
      F.presheafHomObjHomEquiv (ex.hom ≫ φ ≫ ey.inv) := sorry

end Pseudofunctor

end CategoryTheory
