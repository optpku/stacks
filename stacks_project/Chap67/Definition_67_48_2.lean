/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.IntegralClosure
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory

/- Definition 67.48.2: for a scheme `S`, an algebraic space `X` over `S`, and a
quasi-coherent sheaf `A` of `𝒪_X`-algebras, the integral closure of `𝒪_X` in `A`
is the quasi-coherent `𝒪_X`-subalgebra `A' ⊂ A` constructed in Lemma 67.48.1. -/
@[stacks 0821] #check (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.integralClosure :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S},
    AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder X →
      AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder X)

/- The inclusion of the integral closure as a quasi-coherent `𝒪_X`-subalgebra of `A`. -/
#check (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.inclusion :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    (A : AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder X),
      AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.integralClosure A ⟶ A)
