module

public import ReasLib.AlgebraicGeometry.FormalDeformation.CompletionFunctoriality
import StacksCheckRecall

/-!
# Completion as a 2-functor on categories cofibered in groupoids

Completion preserves complete local bases and acts stagewise on objects, morphisms,
functors, and vertical natural transformations.
-/

@[expose] public section

open CategoryTheory CofiberedCategoryOver.Groupoids
open scoped BasedFunctor Bicategory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Remark 90.7.8: completion sends `(R, ξₙ, fₙ)` to `(R, φ.obj ξₙ, φ.map fₙ)`
under a based functor `φ`, sends `(a₀, aₙ)` to `(a₀, φ.map aₙ)`, and sends a
vertical transformation `t` to the transformation with identity base map and
stage components `t.app ξₙ`. These actions assemble into a strict 2-functor. -/
@[stacks 06H9] #check (CategoryTheory.Functor.completionStrictPseudofunctor :
  StrictPseudofunctor
    (CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k))
    (CofiberedCategoryOver.Groupoids.{u + 1, u, max (u + 1) v, max u v}
      (CompleteLocalAlgCat Λ k)))

#check (CategoryTheory.Functor.completionStrictPseudofunctor_obj :
  ∀ X : CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k),
    (Functor.completionStrictPseudofunctor.obj X).p = Functor.completion X.p)

#check (CategoryTheory.Functor.completionStrictPseudofunctor_map :
  ∀ {X Y : CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k)}
    (φ : X ⟶ Y),
    toBasedFunctor (Functor.completionStrictPseudofunctor.map φ) =
      FormalObject.basedMap (toBasedFunctor φ))

#check (CategoryTheory.Functor.completionStrictPseudofunctor_map₂ :
  ∀ {X Y : CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k)}
    {φ φ' : X ⟶ Y} (t : φ ⟶ φ'),
    toBasedNatTrans (Functor.completionStrictPseudofunctor.map₂ t) =
      FormalObject.basedMap₂ (toBasedNatTrans t))
