/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ProjectiveSpace.Beilinson.EndomorphismAlgebra

universe u

/- 36.20.0.2: The endomorphism algebra of `⨁ i, 𝒪(-i)` on projective space is
the algebra of matrices whose row-`i`, column-`j` entry is homogeneous of degree `j - i`. -/
@[stacks 0CS9] #check
  (AlgebraicGeometry.ProjectiveSpace.Beilinson.toEnd_bijective :
    ∀ (A : Type u) [CommRing A] (n : ℕ),
      Function.Bijective (AlgebraicGeometry.ProjectiveSpace.Beilinson.toEnd A n))
