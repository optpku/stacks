module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.Quotient

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

variable (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))

/- Definition 90.27.1: the actual quotient presentation and its formal object. -/
#check (CategoryTheory.GroupoidInFunctors.quotientMorphism G :
  BasedCategory.ofFunctor (CategoryOfElements.π G.U) ⥤ᵇ
    BasedCategory.ofFunctor G.forget)
#check (CategoryTheory.GroupoidInFunctors.quotientMorphismULift G :
  BasedCategory.ofFunctor (FormalObject.elementsProjectionULift G.U) ⥤ᵇ
    BasedCategory.ofFunctor G.forgetULift)
#check (CategoryTheory.GroupoidInFunctors.quotientFormalObject G :
  ∀ {R : CompleteLocalAlgCat Λ k},
    (G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) → FormalObject G.forgetULift)
#check (CategoryTheory.GroupoidInFunctors.quotientStageMap G :
  ∀ {R : CompleteLocalAlgCat Λ k}
    (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) (n : ℕ),
    G.quotientStage e (n + 1) ⟶ G.quotientStage e n)
