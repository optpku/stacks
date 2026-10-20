module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth

/-!
# Smooth morphisms of categories cofibered in groupoids

A morphism of categories cofibered in groupoids over `ArtinianLocalAlgCat Λ k` is
smooth when it satisfies the infinitesimal lifting property along surjections.
-/

@[expose] public section

open CategoryTheory

universe u v w v' w'

#check (CategoryTheory.BasedFunctor.IsSmooth.spec :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k]
    {X : BasedCategory.{v, w} (ArtinianLocalAlgCat Λ k)}
    {Y : BasedCategory.{v', w'} (ArtinianLocalAlgCat Λ k)}
    [Functor.IsFibered.InGroupoids X.p.op] [Functor.IsFibered.InGroupoids Y.p.op]
    (φ : X ⥤ᵇ Y) [BasedFunctor.IsSmooth φ]
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A), Function.Surjective f.hom →
    ∀ {y : Y.obj} {x : X.obj} (α : y ⟶ φ.obj x), Y.p.IsHomLift f α →
      ∃ (x' : X.obj) (β : x' ⟶ x) (γ : φ.obj x' ⟶ y),
        X.p.IsHomLift f β ∧ Y.p.IsHomLift (𝟙 B) γ ∧ γ ≫ α = φ.map β)
