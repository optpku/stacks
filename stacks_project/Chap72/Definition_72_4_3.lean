/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.GenericPoint
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 72.4.3: Let `S` be a scheme. Let `X` be an integral algebraic space over `S`.

The function field, or the field of rational functions of `X`, is the existing

rational-function ring `R(X)` of an integral algebraic space, i.e. `RationalFunction X`

bundled as `rationalFunctionRing X`, equipped with its field structure. -/

@[stacks 0ENE] #check

  (AlgebraicGeometry.AlgebraicSpace.instField_rationalFunctionRing :

    forall {S : Scheme.{u}} {X : AlgebraicSpace S} [IsIntegral X],

      Field (AlgebraicGeometry.AlgebraicSpace.RationalFunction X))



#check

  (AlgebraicGeometry.AlgebraicSpace.rationalFunctionRing :

    {S : Scheme.{u}} -> AlgebraicSpace S ->

      CommRingCat.{u + 1})



#check

  (AlgebraicGeometry.AlgebraicSpace.RationalFunction :

    {S : Scheme.{u}} -> AlgebraicSpace S -> Type (u + 1))

