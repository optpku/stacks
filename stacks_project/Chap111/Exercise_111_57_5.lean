/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.ProjectiveAffineCover
import StacksCheckRecall

/-!
# Exercise 111.57.5

A projective variety over a field admits a surjective morphism from some affine
variety over the same field.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProjectiveVariety

/- Exercise 111.57.5 (0AAR): let `k` be a field and let `X` be a projective variety
over `k`. There exist an affine variety `U` over `k` and a surjective morphism
of varieties `U ⟶ X`. -/
@[stacks 0AAR] #check
  (AlgebraicGeometry.ProjectiveVariety.exists_affine_surjective :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [ProjectiveVariety X],
      ∃ (U : SchemeOverField k) (hU : AffineVariety U) (f : U ⟶ X),
        Surjective f.left)

end AlgebraicGeometry.ProjectiveVariety
