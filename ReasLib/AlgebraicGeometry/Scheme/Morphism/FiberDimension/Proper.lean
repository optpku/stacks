module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.Semicontinuity.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.Target

/-!
# Upper semicontinuity of fibre dimensions

For proper morphisms of schemes, the target-indexed dimension of the fibres is upper
semicontinuous.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a proper morphism of schemes, the target-indexed fibre-dimension function is upper
semicontinuous. -/
theorem upperSemicontinuous_fiberDimension {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] : UpperSemicontinuous f.fiberDimension := sorry

end AlgebraicGeometry.Scheme.Hom
