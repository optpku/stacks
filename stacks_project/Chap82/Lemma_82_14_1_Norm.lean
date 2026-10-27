/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.Norm

/-!
# Function-field norms of morphisms of integral algebraic spaces

The induced rational-function map, explicit algebra, and unit norm are provided
by their mathematical owners. The checks below record their complete interfaces.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Hom.rationalFunctionMap :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ Y) [Dominant p], RationalFunction Y →+* RationalFunction X)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.rationalFunctionAlgebra :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ Y) [Dominant p], Algebra (RationalFunction Y) (RationalFunction X))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.algebraMap_rationalFunctionAlgebra :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ Y) [Dominant p],
    -- Local instance justification (instance diamond): distinct dominant morphisms induce competing algebras on the same pair of rational-function fields.
    letI : Algebra (RationalFunction Y) (RationalFunction X) :=
      rationalFunctionAlgebra p
    algebraMap (RationalFunction Y) (RationalFunction X) = rationalFunctionMap p)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.inducedRationalFunctionNorm :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ Y) [Dominant p], (RationalFunction X)ˣ →* (RationalFunction Y)ˣ)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.inducedRationalFunctionNorm_apply :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ Y) [Dominant p] (φ : (RationalFunction X)ˣ),
    -- Local instance justification (instance diamond): distinct dominant morphisms induce competing algebras on the same pair of rational-function fields.
    letI : Algebra (RationalFunction Y) (RationalFunction X) :=
      rationalFunctionAlgebra p
    (inducedRationalFunctionNorm p φ : RationalFunction Y) =
      Algebra.norm (RationalFunction Y) (φ : RationalFunction X))
