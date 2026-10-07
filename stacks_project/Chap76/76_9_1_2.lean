module

import StacksCheckRecall
import stacks_project.Chap76.«76_9_1_2_Equivalence»

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Thickening

universe u

/- 76.9.1.2: if `i : X ⟶ X'` is a thickening of algebraic spaces, the
spaces-étale sites are identified by 76.9.1.1, so `𝒪_{X'}` may be viewed on
`X_spaces,étale`. This yields a canonical equivalence of locally ringed topoi
`(Sh(X'_spaces,étale), 𝒪_{X'}) ≅ (Sh(X_spaces,étale), 𝒪_{X'})` via
`closedRingedToposHom`. -/
@[stacks 05ZM] #check
  (closedRingedToposHom_isEquivalence_of_isThickening :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X') [IsThickening i],
      (closedRingedToposHom i).IsEquivalence)
