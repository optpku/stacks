module

public import Mathlib.Topology.Semicontinuity.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberDimension.Target
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

/-!
# Lower semicontinuity of fibre dimensions of flat morphisms of algebraic spaces

The target-indexed fibre dimension of a flat morphism of finite presentation of
algebraic spaces is lower semicontinuous on the space of points of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The target-indexed fibre-dimension function of a flat morphism of finite
presentation of algebraic spaces over a scheme is lower semicontinuous. -/
theorem lowerSemicontinuous_fiberDimension {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Flat f] [FinitePresentation f] :
    LowerSemicontinuous (fiberDimension f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
