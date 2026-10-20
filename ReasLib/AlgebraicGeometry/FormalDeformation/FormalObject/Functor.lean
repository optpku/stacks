module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Existence
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.DualNumber

/-!
# Versal formal objects of predeformation functors

Schlessinger's first two conditions and finite-dimensionality of the canonical
tangent space imply existence of a versal formal object of the associated cofibered set.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- A predeformation functor satisfying Schlessinger's first two conditions with
finite-dimensional canonical tangent space admits a versal formal object of its
lifted category-of-elements projection. -/
theorem exists_isVersal_pi (F : ArtinianLocalAlgCat Λ k ⥤ Type u)
    [IsPredeformationFunctor F] [HasSchlessingerH1 F] [HasSchlessingerH2 F]
    [FiniteDimensional k (IsPredeformationFunctor.tangentSpace F)] :
    ∃ ξ : FormalObject (FormalObject.elementsProjectionULift F),
      FormalObject.IsVersal ξ := sorry

end CategoryTheory.Functor
