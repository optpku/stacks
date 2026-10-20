/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.Flattening
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.Preservation

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
