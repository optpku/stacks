module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety

/-!
# Geometric integrality of varieties

This file relates rational smooth points on varieties to geometric integrality.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- A variety over a field is geometrically integral if it has a rational point at which its
structure morphism is smooth. -/
theorem geometricallyIntegral_of_smoothAt_of_rationalPoint
    (X : Over (Spec (CommRingCat.of k))) [Variety X] (x : X.left)
    [IsIso (X.hom.residueFieldMap x)] (h_smooth : X.hom.SmoothAt x) :
    GeometricallyIntegral X.hom := sorry

end AlgebraicGeometry
