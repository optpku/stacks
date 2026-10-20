module

public import Mathlib.Topology.LocallyConstant.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberDimension.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberDimension.Proper

/-!
# Local constancy of fibre dimensions of proper flat morphisms of algebraic spaces

The target-indexed fibre dimension of a proper, flat, finitely presented morphism of
algebraic spaces is locally constant on the space of points of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The target-indexed fibre-dimension function of a proper, flat, finitely
presented morphism of algebraic spaces over a scheme is locally constant. -/
theorem isLocallyConstant_fiberDimension {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f] :
    IsLocallyConstant (fiberDimension f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
