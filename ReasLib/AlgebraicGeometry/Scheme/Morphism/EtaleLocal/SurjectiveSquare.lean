module

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.OpenImmersion

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A property of scheme morphisms is étale local in surjective squares if it has the same
truth value on the horizontal maps of every commutative square whose vertical maps are
surjective and étale. -/
class IsEtaleLocalInSurjectiveSquares (P : MorphismProperty Scheme.{u}) : Prop where
  /-- The property is invariant between the horizontal maps of a commutative square with
  surjective étale vertical maps. -/
  iff_of_square {U V X Y : Scheme.{u}} (h : U ⟶ V) (a : U ⟶ X)
      (b : V ⟶ Y) (f : X ⟶ Y) (sq : CommSq h a b f)
      [Etale a] [Surjective a] [Etale b] [Surjective b] :
    P h ↔ P f

namespace IsEtaleLocalAtSourceAndTarget

variable (P : MorphismProperty Scheme.{u})

/-- Étale locality on source-and-target implies invariance in commutative squares whose
vertical maps are surjective and étale. -/
instance toIsEtaleLocalInSurjectiveSquares [IsEtaleLocalAtSourceAndTarget P] :
    IsEtaleLocalInSurjectiveSquares P := sorry

end IsEtaleLocalAtSourceAndTarget

namespace IsEtaleLocalInSurjectiveSquares

variable (P : MorphismProperty Scheme.{u})

/-- Invariance in surjective étale squares implies étale locality on the source for a
property compatible with étale restriction, coproducts, and open-immersion
postcomposition. -/
instance toIsLocalAtSource [IsEtaleLocalInSurjectiveSquares P]
    [P.RespectsLeft (@Etale : MorphismProperty Scheme.{u})]
    [P.IsStableUnderCoproducts.{u}]
    [P.RespectsRight (@IsOpenImmersion : MorphismProperty Scheme.{u})] :
    P.IsLocalAtSource Scheme.etalePrecoverage := sorry

/-- Invariance in surjective étale squares implies étale locality on the target for a
property compatible with étale base change and coproducts. -/
instance toIsLocalAtTarget [IsEtaleLocalInSurjectiveSquares P]
    [P.IsStableUnderBaseChangeAgainst (@Etale : MorphismProperty Scheme.{u})]
    [P.IsStableUnderCoproducts.{u}] :
    P.IsLocalAtTarget Scheme.etalePrecoverage := sorry

/-- For a property compatible with étale restriction, étale base change, coproducts, and
open-immersion postcomposition, invariance in surjective étale squares is equivalent to
étale locality on source-and-target. -/
theorem iff_sourceAndTarget_of_respectsRightOpenImmersion
    (P : MorphismProperty Scheme.{u})
    [P.RespectsLeft (@Etale : MorphismProperty Scheme.{u})]
    [P.IsStableUnderBaseChangeAgainst (@Etale : MorphismProperty Scheme.{u})]
    [P.IsStableUnderCoproducts.{u}]
    [P.RespectsRight (@IsOpenImmersion : MorphismProperty Scheme.{u})] :
    IsEtaleLocalInSurjectiveSquares P ↔ IsEtaleLocalAtSourceAndTarget P := sorry

end IsEtaleLocalInSurjectiveSquares

end AlgebraicGeometry
