module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Completion.HomEquivalence
import StacksCheckRecall

@[expose] public section

open CategoryTheory CofiberedCategoryOver.Groupoids
open scoped BasedFunctor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Remark 90.7.9: completion and restriction are 2-adjoint in the hom-category sense.
The forward functor composes the truncation-pushforward unit with the completed morphism;
the specified quasi-inverse restricts a morphism and composes it with canonical evaluation. -/
@[stacks 06HA] #check (CategoryTheory.CofiberedCategoryOver.Groupoids.homEquivFunctor.isEquivalence :
  ∀ (F : CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k))
    (G : CofiberedCategoryOver.Groupoids.{u + 1, u, max (u + 1) v, max u v}
      (CompleteLocalAlgCat Λ k)),
    (CategoryTheory.CofiberedCategoryOver.Groupoids.homEquivFunctor F G).IsEquivalence)

#check (CategoryTheory.CofiberedCategoryOver.Groupoids.homEquivInverse :
  ∀ (F : CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k))
    (G : CofiberedCategoryOver.Groupoids.{u + 1, u, max (u + 1) v, max u v}
      (CompleteLocalAlgCat Λ k)),
    (G.toBasedCategory ⥤ᵇ BasedCategory.ofFunctor (Functor.completion F.p)) ⥤
      ((restrictInclusion G).toBasedCategory ⥤ᵇ F.toBasedCategory))

#check (CategoryTheory.CofiberedCategoryOver.Groupoids.homEquivInverse_isQuasiInverse :
  ∀ (F : CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k))
    (G : CofiberedCategoryOver.Groupoids.{u + 1, u, max (u + 1) v, max u v}
      (CompleteLocalAlgCat Λ k)),
    Nonempty (Functor.id _ ≅ homEquivFunctor F G ⋙ homEquivInverse F G) ∧
      Nonempty (homEquivInverse F G ⋙ homEquivFunctor F G ≅ Functor.id _))

#check (CategoryTheory.CofiberedCategoryOver.Groupoids.completionCounit_isEquivalence :
  ∀ (F : CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k)),
    BasedFunctor.IsEquivalence (completionCounit F))
