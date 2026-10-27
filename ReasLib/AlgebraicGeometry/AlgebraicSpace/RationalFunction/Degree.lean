/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.Morphism

/-! # Degrees of dominant morphisms of integral algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The degree `[R(X) : R(Y)]` of the function-field extension induced by a
dominant morphism of integral algebraic spaces. -/
noncomputable def inducedFunctionFieldDegree {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [Dominant f] : ℕ :=
  -- Local instance justification (instance diamond): distinct dominant morphisms induce competing algebras on the same pair of rational-function fields.
  letI : Algebra (RationalFunction Y) (RationalFunction X) :=
    rationalFunctionAlgebra f
  Module.finrank (RationalFunction Y) (RationalFunction X)

/-- The induced function-field degree is the finrank of `R(X)` as an `R(Y)`-module
for the morphism-local algebra `rationalFunctionAlgebra`. -/
theorem inducedFunctionFieldDegree_eq_finrank {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [Dominant f] :
    inducedFunctionFieldDegree f =
      -- Local instance justification (instance diamond): distinct dominant morphisms induce competing algebras on the same pair of rational-function fields.
      letI : Algebra (RationalFunction Y) (RationalFunction X) :=
        rationalFunctionAlgebra f
      Module.finrank (RationalFunction Y) (RationalFunction X) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Hom
