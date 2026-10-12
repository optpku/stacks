/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap77.«77_7_8_1_Flattening»
public import stacks_project.Chap77.Lemma_77_7_4_Limit

/-!
# Limit preservation for the flattening functor on algebraic spaces

This module records preservation of directed inverse limits of affine schemes
by the functor detecting flatness after base change to a scheme over an
algebraic space.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.Flattening

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ℱ : X.Modules)
variable [QuasiCompact f] [LocallyOfFinitePresentation f] [ℱ.IsFinitePresentation]

/-- For a finitely presented module over a quasi-compact, locally finitely
presented morphism of algebraic spaces, the flattening functor preserves
directed inverse limits of affine schemes over the base. -/
theorem functor_preservesDirectedAffineLimits :
    SchemeOver.PreservesDirectedAffineLimits Y (functor f ℱ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.Flattening
