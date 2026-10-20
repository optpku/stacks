module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth.SmallExtension
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open ArtinianLocalAlgCat (IsSmallExtension)

universe u v w v' w'

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Lemma 90.8.2: a morphism `φ` of categories cofibered in groupoids over
`ArtinianLocalAlgCat Λ k` is smooth if the infinitesimal lifting property of
Definition 90.8.1 is assumed only along small extensions `B ⟶ A`. -/
@[stacks 06HH] #check (CategoryTheory.BasedFunctor.isSmooth_of_exists_lift_isSmallExtension :
  ∀ {X : BasedCategory.{v, w} (ArtinianLocalAlgCat Λ k)}
    {Y : BasedCategory.{v', w'} (ArtinianLocalAlgCat Λ k)}
    [Functor.IsFibered.InGroupoids X.p.op] [Functor.IsFibered.InGroupoids Y.p.op]
    (φ : X ⥤ᵇ Y)
    (h : ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) [IsSmallExtension f]
      {y : Y.obj} {x : X.obj} (α : y ⟶ φ.obj x), Y.p.IsHomLift f α →
        ∃ (x' : X.obj) (β : x' ⟶ x) (γ : φ.obj x' ⟶ y),
          X.p.IsHomLift f β ∧ Y.p.IsHomLift (𝟙 B) γ ∧ γ ≫ α = φ.map β),
    CategoryTheory.BasedFunctor.IsSmooth φ)
