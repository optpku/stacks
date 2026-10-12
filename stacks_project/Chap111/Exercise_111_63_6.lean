/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.TwoUple
public import Mathlib.FieldTheory.IsAlgClosed.Basic

universe u

/- Exercise 111.63.6: over an algebraically closed field `k`, the 2-uple embedding
`ProjectiveSpace.scheme k 2 ⟶ ProjectiveSpace.scheme k 5` is the morphism associated to
`twistingSheaf k 2 2`, given in homogeneous coordinates by
`[a₀ : a₁ : a₂] ↦ [a₀ ^ 2 : a₀ * a₁ : a₀ * a₂ : a₁ ^ 2 : a₁ * a₂ : a₂ ^ 2]`, and is a closed
immersion. If `I` is the homogeneous ideal of the image, so that the degree-`d` piece consists of
the degree-`d` forms restricting to zero on that closed subscheme, then
`Module.finrank k (idealDegree k d) = (5 + 1).multichoose d - (2 + 1).multichoose (2 * d)`. -/
@[stacks 0G18] #check (AlgebraicGeometry.ProjectiveSpace.TwoUple.finrank_idealDegree :
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ),
    Module.finrank k (AlgebraicGeometry.ProjectiveSpace.TwoUple.idealDegree k d) =
      (5 + 1).multichoose d - (2 + 1).multichoose (2 * d))
