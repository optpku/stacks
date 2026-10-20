/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothCategory

/-!
# Smooth or unobstructed categories cofibered in groupoids

A category cofibered in groupoids over `ArtinianLocalAlgCat Λ k` is smooth, or
unobstructed, when its structure morphism is a smooth morphism of categories
cofibered in groupoids.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type w} [Category.{v} F]

/- The lifting specification of a smooth category cofibered in groupoids. -/
#check (CategoryTheory.Functor.IsSmooth.exists_lift :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type w} [Category.{v} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op]
    [CategoryTheory.Functor.IsSmooth p]
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) (hf : Function.Surjective f.hom)
    {y : ArtinianLocalAlgCat Λ k} {x : F} (α : y ⟶ p.obj x)
    (hα : (𝟭 (ArtinianLocalAlgCat Λ k)).IsHomLift f α),
    ∃ (x' : F) (β : x' ⟶ x) (γ : p.obj x' ⟶ y),
      p.IsHomLift f β ∧ (𝟭 (ArtinianLocalAlgCat Λ k)).IsHomLift (𝟙 B) γ ∧
        γ ≫ α = p.map β)
