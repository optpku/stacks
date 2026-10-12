/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Polynomial
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

variable (A : Type u) [CommRing A]

/- Exercise 111.53.6: for a ring `A` and `S = A[X]` with `X` in degree `1`,
`Proj(S)` is canonically isomorphic to `Spec(A)` as schemes over `A`. -/
@[stacks 069W] #check
  (AlgebraicGeometry.PolynomialProj.toSpec_isIso A :
    IsIso (AlgebraicGeometry.PolynomialProj.toSpec A))
