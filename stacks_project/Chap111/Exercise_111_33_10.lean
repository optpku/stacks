/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.NonLocalSpecHom
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

/- Exercise 111.33.10: the morphism of ringed spaces `hom : Spec ℚ ⟶ Spec ℤ` sending
the unique point to `(2)` is not a morphism of schemes. -/
@[stacks 028W] #check (AlgebraicGeometry.NonLocalSpecHom.not_isSchemeHom :
  ¬ ∃ f : AlgebraicGeometry.NonLocalSpecHom.ratSpec ⟶
      AlgebraicGeometry.NonLocalSpecHom.intScheme,
    LocallyRingedSpace.forgetToSheafedSpace.map f.toLRSHom =
      AlgebraicGeometry.NonLocalSpecHom.hom)
