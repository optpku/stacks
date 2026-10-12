/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.Product.Cohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Exercise 111.44.7: over a field `k`, on the product `X` of the projective line
with itself, the sheaf `𝒪(a, b) = p^* 𝒪(a) ⊗ q^* 𝒪(b)` has the stated cohomology
finrank formula in every degree. -/
@[stacks 0DBA] #check
  (AlgebraicGeometry.ProjectiveLine.Product.cohomologyFinrank_twistingSheaf :
    ∀ (k : Type u) [Field k] (a b : ℤ) (i : ℕ),
      Scheme.Hom.cohomologyFinrank
          (AlgebraicGeometry.ProjectiveLine.Product.toSpec k)
          (AlgebraicGeometry.ProjectiveLine.Product.twistingSheaf k a b) i =
        AlgebraicGeometry.ProjectiveLine.Product.twistingSheafCohomologyFinrank a b i)
