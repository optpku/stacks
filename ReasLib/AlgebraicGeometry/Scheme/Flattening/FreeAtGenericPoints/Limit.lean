/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Flattening.FreeAtGenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation

/-!
# Limit preservation for freeness at generic points

This module records preservation of directed affine limits by the functor detecting fixed-rank
freeness near every generic point of a fibre.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Flattening

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) (p : ℕ)
variable [Smooth f] [GeometricallyIrreducible f]

/-- For a finitely presented module, the functor detecting fixed-rank freeness near every fibre
generic point preserves directed limits of affine schemes over the base. -/
theorem freeAtGenericPointsFunctor_preservesDirectedAffineLimits
    [ℱ.IsFinitePresentation] :
    Scheme.Over.PreservesDirectedAffineLimits S
      (freeAtGenericPointsFunctor f ℱ p) := sorry

end AlgebraicGeometry.Scheme.Flattening
