/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap77.«77_11_4_1_Functor»
public import stacks_project.Chap77.Lemma_77_7_4_Limit

/-!
# Limit preservation for the flat-in-dimensions functor on algebraic spaces

This module records preservation of directed inverse limits of affine schemes
by the functor detecting flatness in dimensions at least a fixed natural number
after base change to a scheme over an algebraic space.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Flattening

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ℱ : X.Modules)
variable [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (n : ℕ)
variable [QuasiCompact f] [LocallyOfFinitePresentation f] [ℱ.IsFinitePresentation]

/-- For a finitely presented module over a quasi-compact, locally finitely
presented morphism of algebraic spaces, the functor detecting flatness in
dimensions at least `n` preserves directed inverse limits of affine schemes
over the base. -/
theorem flatInDimensionsFunctor_preservesDirectedAffineLimits :
    SchemeOver.PreservesDirectedAffineLimits Y (flatInDimensionsFunctor f ℱ n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Flattening
