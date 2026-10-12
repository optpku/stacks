/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.Basic

/-!
# Endpoint actions on canonical Hom-presheaves

For a fixed fiber of a `Cat`-valued pseudofunctor, this module supplies the
contravariant and covariant actions on its canonical Hom-presheaves. The
two-endpoint functor and its laws are in `Endpoint.Functoriality`.
-/

@[expose] public section

universe uC vC uP vP

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

namespace Pseudofunctor

variable {C : Type uC} [Category.{vC} C]

/-- Naturality of postcomposition by a fixed fiber morphism on the canonical Hom-presheaf. -/
theorem PresheafHom.Postcomp.naturality
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x y z : F.obj (.mk (op U))} (ψ : y ⟶ z) :
    ∀ ⦃W₁ W₂ : (Over U)ᵒᵖ⦄ (α : W₁ ⟶ W₂),
      (F.presheafHom x y).map α ≫
          TypeCat.ofHom
            (fun φ ↦ φ ≫ (F.map W₂.unop.hom.op.toLoc).toFunctor.map ψ) =
        TypeCat.ofHom
            (fun φ ↦ φ ≫ (F.map W₁.unop.hom.op.toLoc).toFunctor.map ψ) ≫
          (F.presheafHom x z).map α := sorry

/-- Postcomposition by a fixed fiber morphism, as a natural transformation of canonical
Hom-presheaves. -/
def PresheafHom.Postcomp.map
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x y z : F.obj (.mk (op U))} (ψ : y ⟶ z) :
    F.presheafHom x y ⟶ F.presheafHom x z where
  app W :=
    TypeCat.ofHom
      (fun φ ↦ φ ≫ (F.map W.unop.hom.op.toLoc).toFunctor.map ψ)
  naturality := PresheafHom.Postcomp.naturality F ψ

/-- A component of Hom-presheaf postcomposition applies the restricted image of the fixed
morphism on the right. -/
@[simp]
theorem PresheafHom.Postcomp.app
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x y z : F.obj (.mk (op U))} (ψ : y ⟶ z)
    (W : (Over U)ᵒᵖ) :
    (PresheafHom.Postcomp.map F (x := x) ψ).app W =
      TypeCat.ofHom
        (fun φ : (F.presheafHom x y).obj W ↦
          φ ≫ (F.map W.unop.hom.op.toLoc).toFunctor.map ψ) := sorry

/-- Elementwise computation of Hom-presheaf postcomposition. -/
@[simp]
theorem PresheafHom.Postcomp.appApply
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x y z : F.obj (.mk (op U))} (ψ : y ⟶ z)
    (W : (Over U)ᵒᵖ) (φ : (F.presheafHom x y).obj W) :
    (PresheafHom.Postcomp.map F ψ).app W φ =
      φ ≫ (F.map W.unop.hom.op.toLoc).toFunctor.map ψ := sorry

/-- At the identity slice, Hom-presheaf postcomposition is ordinary postcomposition. -/
@[simp]
theorem PresheafHom.Postcomp.identitySlice
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x y z : F.obj (.mk (op U))}
    (ψ : y ⟶ z) (φ : x ⟶ y) :
    (PresheafHom.Postcomp.map F ψ).app (op (Over.mk (𝟙 U)))
        (F.presheafHomObjHomEquiv φ) =
      F.presheafHomObjHomEquiv (φ ≫ ψ) := sorry

/-- Naturality of precomposition by a fixed fiber morphism on the canonical Hom-presheaf. -/
theorem PresheafHom.Precomp.naturality
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x y z : F.obj (.mk (op U))} (φ : x ⟶ y) :
    ∀ ⦃W₁ W₂ : (Over U)ᵒᵖ⦄ (α : W₁ ⟶ W₂),
      (F.presheafHom y z).map α ≫
          TypeCat.ofHom
            (fun ψ ↦ (F.map W₂.unop.hom.op.toLoc).toFunctor.map φ ≫ ψ) =
        TypeCat.ofHom
            (fun ψ ↦ (F.map W₁.unop.hom.op.toLoc).toFunctor.map φ ≫ ψ) ≫
          (F.presheafHom x z).map α := sorry

/-- Precomposition by a fixed fiber morphism, as a natural transformation of canonical
Hom-presheaves. -/
def PresheafHom.Precomp.map
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x y z : F.obj (.mk (op U))} (φ : x ⟶ y) :
    F.presheafHom y z ⟶ F.presheafHom x z where
  app W :=
    TypeCat.ofHom
      (fun ψ ↦ (F.map W.unop.hom.op.toLoc).toFunctor.map φ ≫ ψ)
  naturality := PresheafHom.Precomp.naturality F φ

/-- A component of Hom-presheaf precomposition applies the restricted image of the fixed
morphism on the left. -/
@[simp]
theorem PresheafHom.Precomp.app
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x y z : F.obj (.mk (op U))} (φ : x ⟶ y)
    (W : (Over U)ᵒᵖ) :
    (PresheafHom.Precomp.map F (z := z) φ).app W =
      TypeCat.ofHom
        (fun ψ : (F.presheafHom y z).obj W ↦
          (F.map W.unop.hom.op.toLoc).toFunctor.map φ ≫ ψ) := sorry

/-- Elementwise computation of Hom-presheaf precomposition. -/
@[simp]
theorem PresheafHom.Precomp.appApply
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x y z : F.obj (.mk (op U))} (φ : x ⟶ y)
    (W : (Over U)ᵒᵖ) (ψ : (F.presheafHom y z).obj W) :
    (PresheafHom.Precomp.map F φ).app W ψ =
      (F.map W.unop.hom.op.toLoc).toFunctor.map φ ≫ ψ := sorry

/-- At the identity slice, Hom-presheaf precomposition is ordinary precomposition. -/
@[simp]
theorem PresheafHom.Precomp.identitySlice
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x y z : F.obj (.mk (op U))}
    (φ : x ⟶ y) (ψ : y ⟶ z) :
    (PresheafHom.Precomp.map F φ).app (op (Over.mk (𝟙 U)))
        (F.presheafHomObjHomEquiv ψ) =
      F.presheafHomObjHomEquiv (φ ≫ ψ) := sorry

end Pseudofunctor

end CategoryTheory
