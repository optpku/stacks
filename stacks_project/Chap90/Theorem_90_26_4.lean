module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.Presentation
import StacksCheckRecall

/-!
# Presentations of deformation categories

A category cofibered in groupoids over `ArtinianLocalAlgCat Λ k` admits a presentation
by a smooth prorepresentable groupoid in functors if and only if it is a deformation
category whose tangent space and infinitesimal automorphism space are finite-dimensional
over `k`.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open Functor
open ArtinianLocalAlgCat
open scoped Bicategory BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

variable {F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
    (ArtinianLocalAlgCat Λ k)}
variable {G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)}

/- Theorem 90.26.4: a category cofibered in groupoids admits a smooth
prorepresentable presentation exactly when it is a deformation category and its
tangent and infinitesimal automorphism spaces are finite-dimensional. -/
@[stacks 06L8] #check
  (CategoryTheory.GroupoidInFunctors.exists_smoothProrepresentablePresentation_iff :
    ∀ (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k)),
    (∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
      (φ : G.quotient ⟶ F),
      IsSmooth G.s G.t ∧ IsProrepresentable G ∧ IsPresentation G F φ) ↔
      IsDeformationCategory F.p ∧
        (∀ [IsDeformationCategory F.p],
          FiniteDimensional k ((fiberIsoClassFunctor F.p).obj (dualNumber Λ k)) ∧
            FiniteDimensional k (infinitesimalAutomorphisms F.p)))

-- A smooth prorepresentable presentation implies the deformation-category condition.
#check (CategoryTheory.GroupoidInFunctors.isDeformationCategory_of_isPresentation :
  ∀ (φ : G.quotient ⟶ F) [IsSmooth G.s G.t] [IsProrepresentable G],
    IsPresentation G F φ → IsDeformationCategory F.p)

-- A presented deformation category has finite-dimensional tangent space.
#check (CategoryTheory.GroupoidInFunctors.finiteDimensional_tangentSpace_of_isPresentation :
  ∀ (φ : G.quotient ⟶ F) [IsSmooth G.s G.t] [IsProrepresentable G]
    [IsDeformationCategory F.p],
    IsPresentation G F φ →
      FiniteDimensional k ((fiberIsoClassFunctor F.p).obj (dualNumber Λ k)))

-- A presented deformation category has finite-dimensional infinitesimal automorphisms.
#check
  (CategoryTheory.GroupoidInFunctors.finiteDimensional_infinitesimalAutomorphisms_of_isPresentation :
    ∀ (φ : G.quotient ⟶ F) [IsSmooth G.s G.t] [IsProrepresentable G]
      [IsDeformationCategory F.p],
      IsPresentation G F φ → FiniteDimensional k (infinitesimalAutomorphisms F.p))

-- The three conditions suffice for the existence of the specified presentation.
#check (CategoryTheory.GroupoidInFunctors.exists_smoothProrepresentablePresentation :
  ∀ (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
    (ArtinianLocalAlgCat Λ k)) [IsDeformationCategory F.p]
    [FiniteDimensional k ((fiberIsoClassFunctor F.p).obj (dualNumber Λ k))]
    [FiniteDimensional k (infinitesimalAutomorphisms F.p)],
    ∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
      (φ : G.quotient ⟶ F),
      IsSmooth G.s G.t ∧ IsProrepresentable G ∧ IsPresentation G F φ)

end CategoryTheory.GroupoidInFunctors
