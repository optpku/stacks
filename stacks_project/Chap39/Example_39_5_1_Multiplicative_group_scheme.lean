/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.MultiplicativeGroup

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.MultiplicativeGroup

universe u

/- Example 39.5.1 (Multiplicative group scheme) (1): the integral model is the spectrum of the
Laurent-polynomial ring. -/
@[stacks 022U] #check (AlgebraicGeometry.MultiplicativeGroup.overInt_left :
  AlgebraicGeometry.MultiplicativeGroup.overInt.left =
    Spec (CommRingCat.of (LaurentPolynomial (ULift.{u} ℤ))))

/- Example 39.5.1 (Multiplicative group scheme) (2): multiplication sends the Laurent coordinate
to its tensor square. -/
@[stacks 022U] #check (AlgebraicGeometry.MultiplicativeGroup.mul_coordinate :
  Bialgebra.comulAlgHom (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ))
      (LaurentPolynomial.T 1) =
    LaurentPolynomial.T 1 ⊗ₜ[ULift.{u} ℤ] LaurentPolynomial.T 1)

/- Example 39.5.1 (Multiplicative group scheme) (3): the integral model is the canonical
commutative group scheme `𝔾ₘ` over `Spec (ULift ℤ)`. -/
@[stacks 022U] #check (AlgebraicGeometry.MultiplicativeGroup.groupScheme :
  CommGrp (Over (Spec (CommRingCat.of (ULift.{u} ℤ)))))

/- Example 39.5.1 (Multiplicative group scheme) (4): the integral model represents global units. -/
@[stacks 022U] #check (AlgebraicGeometry.MultiplicativeGroup.representingIso :
  CategoryTheory.yonedaGrp.obj
      AlgebraicGeometry.MultiplicativeGroup.groupScheme.toGrp ≅
    AlgebraicGeometry.MultiplicativeGroup.points
      (Spec (CommRingCat.of (ULift.{u} ℤ))))

/- Example 39.5.1 (Multiplicative group scheme) (5): every base change `𝔾ₘ[S]` is a canonical
commutative group scheme over `S`. -/
@[stacks 022U] #check (AlgebraicGeometry.MultiplicativeGroup.baseChange :
  (S : Scheme.{u}) → CommGrp (Over S))

/- Example 39.5.1 (Multiplicative group scheme) (6): the base change to `S` represents relative
global units. -/
@[stacks 022U] #check (AlgebraicGeometry.MultiplicativeGroup.baseChangeRepresentingIso :
  (S : Scheme.{u}) →
    CategoryTheory.yonedaGrp.obj
        (AlgebraicGeometry.MultiplicativeGroup.baseChange S).toGrp ≅
      AlgebraicGeometry.MultiplicativeGroup.points S)
