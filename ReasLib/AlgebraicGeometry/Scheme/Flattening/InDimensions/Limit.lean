/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Flattening.InDimensions
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation

/-!
# Limit preservation for flatness in dimensions

This module records preservation of directed affine limits by the functor detecting flatness in
dimensions at least a fixed natural number.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Flattening

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) (n : ℕ)
variable [QuasiCompact f] [LocallyOfFinitePresentation f] [ℱ.IsFinitePresentation]

/-- For a finitely presented module over a quasi-compact, locally finitely presented morphism,
the functor detecting flatness in dimensions at least `n` preserves directed limits of affine
schemes over the base. -/
theorem flatInDimensionsFunctor_preservesDirectedAffineLimits :
    Scheme.Over.PreservesDirectedAffineLimits S
      (flatInDimensionsFunctor f ℱ n) := sorry

end AlgebraicGeometry.Scheme.Flattening
