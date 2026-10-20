module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Flattening
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation

/-!
# Limit preservation for the flattening functor

This module records preservation of directed affine limits by the functor detecting flatness
after scheme base change.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules.Flattening

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)
variable [QuasiCompact f] [LocallyOfFinitePresentation f] [ℱ.IsFinitePresentation]

/-- For a finitely presented module over a quasi-compact, locally finitely presented morphism,
the flattening functor preserves directed limits of affine schemes over the base. -/
theorem functor_preservesDirectedAffineLimits :
    Scheme.Over.PreservesDirectedAffineLimits S (functor f ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules.Flattening
