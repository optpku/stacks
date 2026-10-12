/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Polynomial
import StacksCheckRecall
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u

open AlgebraicGeometry

variable {A : Type u} [CommRing A]

/- Exercise 111.27.6 (1) -/
@[stacks 02EB] #check
  (AlgebraicGeometry.PolynomialProj.toSpec_bijective (A := A) :
    Function.Bijective (AlgebraicGeometry.PolynomialProj.toSpec A).base)

/- Exercise 111.27.6 (2) -/
@[stacks 02EB] #check
  (AlgebraicGeometry.PolynomialProj.toSpec_isHomeomorph (A := A) :
    IsHomeomorph (AlgebraicGeometry.PolynomialProj.toSpec A).base)
