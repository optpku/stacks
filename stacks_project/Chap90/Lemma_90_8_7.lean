/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth.Properties
import StacksCheckRecall

/-!
# Functorial properties of smooth morphisms of cofibered groupoids

Smooth morphisms of categories cofibered in groupoids over
`ArtinianLocalAlgCat Λ k` are closed under composition, cancel on the left of
an essentially surjective morphism, and are stable under 2-fibre-product
base change.
-/

@[expose] public section

open CategoryTheory
open CofiberedCategoryOver.Groupoids
open scoped BasedFunctor Bicategory

universe u v w

/- Lemma 90.8.7. Smooth morphisms compose, cancel after essentially surjective morphisms,
and remain smooth under 2-fibre-product base change. -/
@[stacks 06HM] #check (CategoryTheory.BasedFunctor.instIsSmooth_comp :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k]
    {X Y Z : BasedCategory.{v, w} (ArtinianLocalAlgCat Λ k)}
    [Functor.IsFibered.InGroupoids X.p.op] [Functor.IsFibered.InGroupoids Y.p.op]
    [Functor.IsFibered.InGroupoids Z.p.op] (φ : X ⥤ᵇ Y) (ψ : Y ⥤ᵇ Z)
    [BasedFunctor.IsSmooth φ] [BasedFunctor.IsSmooth ψ], BasedFunctor.IsSmooth (φ ⋙ ψ))

#check (CategoryTheory.BasedFunctor.isSmooth_of_comp_essSurj :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k]
    {X Y Z : BasedCategory.{v, w} (ArtinianLocalAlgCat Λ k)}
    [Functor.IsFibered.InGroupoids X.p.op] [Functor.IsFibered.InGroupoids Y.p.op]
    [Functor.IsFibered.InGroupoids Z.p.op] (φ : X ⥤ᵇ Y) (ψ : Y ⥤ᵇ Z)
    [φ.toFunctor.EssSurj] [BasedFunctor.IsSmooth (φ ⋙ ψ)], BasedFunctor.IsSmooth ψ)

#check (CategoryTheory.BasedFunctor.instIsSmooth_twoFibreProduct_snd :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k]
    {F G G' : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k)}
    (φ : F ⟶ G) (τ : G' ⟶ G) [BasedFunctor.IsSmooth (toBasedFunctor φ)],
    BasedFunctor.IsSmooth
      (toBasedFunctor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} φ τ)))
