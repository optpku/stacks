/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFormula

/-!
# Dimension of smooth scheme morphisms

This file records the pointwise local-dimension formula for smooth morphisms of
locally Noetherian schemes.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- For a smooth morphism of locally Noetherian schemes, the local dimension at a source point
is the local dimension at its image plus the local dimension of the corresponding fiber. -/
theorem Smooth.topologicalKrullDimAt_eq_image_add_fiberDimensionAt
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (hf : Smooth f) (x : X) :
    topologicalKrullDimAt x = topologicalKrullDimAt (f x) + f.fiberDimensionAt x := sorry

end AlgebraicGeometry
