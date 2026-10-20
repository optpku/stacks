module

public import Mathlib.Topology.Semicontinuity.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberDimension.Target
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism

/-!
# Upper semicontinuity of fibre dimensions of proper morphisms of algebraic spaces

The target-indexed fibre dimension of a proper morphism of algebraic spaces is
upper semicontinuous on the canonical topology of the target point space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The target-indexed fibre-dimension function of a proper morphism of algebraic
spaces over a scheme is upper semicontinuous for any canonical topology on the
points of the target. -/
theorem upperSemicontinuous_fiberDimension {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
    {τ : TopologicalSpace (Points Y)} (hτ : IsPointsTopology Y τ) :
    @UpperSemicontinuous (Points Y) (WithBot ℕ∞) τ inferInstance
      (fiberDimension f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
