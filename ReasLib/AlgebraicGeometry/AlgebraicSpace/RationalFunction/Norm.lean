/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.Morphism
public import Mathlib.RingTheory.Norm.Defs

/-!
# Norms on rational-function units

The explicit algebra associated to a dominant morphism of integral algebraic
spaces induces a multiplicative norm on rational-function units.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The norm on rational-function units induced by a dominant morphism of
integral algebraic spaces. For extensions that are not module-finite, this
uses the total algebra norm convention of Mathlib, whose value is one. -/
@[expose]
public noncomputable def inducedRationalFunctionNorm {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Y)
    [Dominant p] : (RationalFunction X)ˣ →* (RationalFunction Y)ˣ :=
  -- Local instance justification (instance diamond): distinct dominant morphisms induce competing algebras on the same pair of rational-function fields.
  letI : Algebra (RationalFunction Y) (RationalFunction X) :=
    rationalFunctionAlgebra p
  Units.map (Algebra.norm (RationalFunction Y))

/-- The underlying value of the induced rational-function norm on units is the
algebra norm. -/
public theorem inducedRationalFunctionNorm_apply {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Y)
    [Dominant p] (φ : (RationalFunction X)ˣ) :
    -- Local instance justification (instance diamond): distinct dominant morphisms induce competing algebras on the same pair of rational-function fields.
    letI : Algebra (RationalFunction Y) (RationalFunction X) :=
      rationalFunctionAlgebra p
    (inducedRationalFunctionNorm p φ : RationalFunction Y) =
      Algebra.norm (RationalFunction Y) (φ : RationalFunction X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
