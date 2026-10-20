module

public import Mathlib.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Basic pullback API for Hom morphisms

This module extends mathlib's `Pseudofunctor.LocallyDiscreteOpToCat.pullHom` with
universe-polymorphic algebraic and proof-irrelevance interfaces used in descent arguments.
-/

@[expose] public section

universe u v uX vX

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]

namespace Pseudofunctor.LocallyDiscreteOpToCat

variable {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vX, uX}}

set_option backward.isDefEq.respectTransparency false in
/-- Pulling a morphism in a Hom presheaf back along a further base morphism preserves
composition. This is the reusable form of restricting a composite. -/
theorem pullHom_comp
    {X₁ X₂ X₃ : C} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} {M₃ : F.obj (.mk (op X₃))}
    {A₀ : C} {f₁ : A₀ ⟶ X₁} {f₂ : A₀ ⟶ X₂} {f₃ : A₀ ⟶ X₃}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (ψ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶
      (F.map f₃.op.toLoc).toFunctor.obj M₃)
    {A₁ : C} (k : A₁ ⟶ A₀) (kf₁ : A₁ ⟶ X₁) (kf₂ : A₁ ⟶ X₂) (kf₃ : A₁ ⟶ X₃)
    (hkf₁ : k ≫ f₁ = kf₁) (hkf₂ : k ≫ f₂ = kf₂)
    (hkf₃ : k ≫ f₃ = kf₃) :
    pullHom (F := F) (X₁ := X₁) (X₂ := X₃) (M₁ := M₁) (M₂ := M₃)
        (f₁ := f₁) (f₂ := f₃) (Y' := A₁) (φ ≫ ψ) k kf₁ kf₃ hkf₁ hkf₃ =
      pullHom (F := F) (X₁ := X₁) (X₂ := X₂) (M₁ := M₁) (M₂ := M₂)
          (f₁ := f₁) (f₂ := f₂) (Y' := A₁) φ k kf₁ kf₂ hkf₁ hkf₂ ≫
        pullHom (F := F) (X₁ := X₂) (X₂ := X₃) (M₁ := M₂) (M₂ := M₃)
          (f₁ := f₂) (f₂ := f₃) (Y' := A₁) ψ k kf₂ kf₃ hkf₂ hkf₃ := sorry

set_option backward.isDefEq.respectTransparency false in
/-- The value of `pullHom` is independent of the proof terms witnessing the two base equalities. -/
theorem pullHom_proof_irrel
    {X₁ X₂ : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {Y Y' : C} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (k : Y' ⟶ Y) (kf₁ : Y' ⟶ X₁) (kf₂ : Y' ⟶ X₂)
    (h₁ h₁' : k ≫ f₁ = kf₁) (h₂ h₂' : k ≫ f₂ = kf₂) :
    pullHom (F := F) φ k kf₁ kf₂ h₁ h₂ =
      pullHom (F := F) φ k kf₁ kf₂ h₁' h₂' := sorry

set_option backward.isDefEq.respectTransparency false in
/-- Equality of two pullback-normalized morphisms induces equality after applying the
corresponding pseudofunctor restriction functor. -/
theorem map_eq_of_pullHom_eq
    {X₁ X₂ : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {Y : C} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    {φ ψ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂}
    {Y' : C} (g : Y' ⟶ Y)
    (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    (hgf₁' : g ≫ f₁ = gf₁) (hgf₂' : g ≫ f₂ = gf₂)
    (hpull :
      pullHom (F := F) φ g gf₁ gf₂ hgf₁ hgf₂ =
        pullHom (F := F) ψ g gf₁ gf₂ hgf₁' hgf₂') :
    (F.map g.op.toLoc).toFunctor.map φ =
      (F.map g.op.toLoc).toFunctor.map ψ := sorry

set_option backward.isDefEq.respectTransparency false in
/-- Pulling back along a base arrow written with a leading identity is the same `pullHom` as
pulling back along the base arrow itself, after explicitly supplying both normalized equalities. -/
theorem pullHom_id_comp_base
    {X₁ X₂ : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {Y : C} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    {Y' : C} (q : Y' ⟶ Y) (qf₁ : Y' ⟶ X₁) (qf₂ : Y' ⟶ X₂)
    (h₁ : (𝟙 Y' ≫ q) ≫ f₁ = qf₁)
    (h₂ : (𝟙 Y' ≫ q) ≫ f₂ = qf₂) :
    pullHom (F := F) φ (𝟙 Y' ≫ q) qf₁ qf₂ h₁ h₂ =
      pullHom (F := F) φ q qf₁ qf₂
        ((congrArg (fun l => l ≫ f₁) (Category.id_comp q)).symm.trans h₁)
        ((congrArg (fun l => l ≫ f₂) (Category.id_comp q)).symm.trans h₂) := sorry

end Pseudofunctor.LocallyDiscreteOpToCat

end CategoryTheory
