module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Factorization

/-!
# Smoothness from small-extension lifts

A morphism of categories cofibered in groupoids over `ArtinianLocalAlgCat Λ k` is
smooth when its infinitesimal lifting property is tested on small extensions.
-/

@[expose] public section

open CategoryTheory
open ArtinianLocalAlgCat (IsSmallExtension)

universe u v w v' w'

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.BasedFunctor

/-- A morphism of categories cofibered in groupoids over `ArtinianLocalAlgCat Λ k`
is smooth if the infinitesimal lifting property holds along every small extension.
-/
theorem isSmooth_of_exists_lift_isSmallExtension
    {X : BasedCategory.{v, w} (ArtinianLocalAlgCat Λ k)}
    {Y : BasedCategory.{v', w'} (ArtinianLocalAlgCat Λ k)}
    [Functor.IsFibered.InGroupoids X.p.op] [Functor.IsFibered.InGroupoids Y.p.op]
    (φ : X ⥤ᵇ Y)
    (h : ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) [IsSmallExtension f]
      {y : Y.obj} {x : X.obj} (α : y ⟶ φ.obj x), Y.p.IsHomLift f α →
        ∃ (x' : X.obj) (β : x' ⟶ x) (γ : φ.obj x' ⟶ y),
          X.p.IsHomLift f β ∧ Y.p.IsHomLift (𝟙 B) γ ∧ γ ≫ α = φ.map β) :
    IsSmooth φ := sorry

/-- Smoothness of a morphism of categories cofibered in groupoids over
`ArtinianLocalAlgCat Λ k` is equivalent to the infinitesimal lifting property
along small extensions.
-/
theorem isSmooth_iff_exists_lift_isSmallExtension
    {X : BasedCategory.{v, w} (ArtinianLocalAlgCat Λ k)}
    {Y : BasedCategory.{v', w'} (ArtinianLocalAlgCat Λ k)}
    [Functor.IsFibered.InGroupoids X.p.op] [Functor.IsFibered.InGroupoids Y.p.op]
    (φ : X ⥤ᵇ Y) :
    IsSmooth φ ↔
      ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) [IsSmallExtension f]
        {y : Y.obj} {x : X.obj} (α : y ⟶ φ.obj x), Y.p.IsHomLift f α →
          ∃ (x' : X.obj) (β : x' ⟶ x) (γ : φ.obj x' ⟶ y),
            X.p.IsHomLift f β ∧ Y.p.IsHomLift (𝟙 B) γ ∧ γ ≫ α = φ.map β := sorry

end CategoryTheory.BasedFunctor
