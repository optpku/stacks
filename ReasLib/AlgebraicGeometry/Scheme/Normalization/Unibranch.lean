module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents.Irreducible
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Stalk.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.Unibranch
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.Properties

/-!
# Normalization of geometrically unibranch schemes

This file records the topological behavior of normalization for irreducible geometrically
unibranch schemes.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The normalization morphism of an irreducible geometrically unibranch scheme is a universal
homeomorphism. -/
theorem universalHomeomorphism_normalizationTo
    (X : Scheme.{u}) [IrreducibleSpace X]
    (hX : X.isGeometricallyUnibranch) :
    UniversalHomeomorphism X.normalizationTo := sorry

end AlgebraicGeometry.Scheme
