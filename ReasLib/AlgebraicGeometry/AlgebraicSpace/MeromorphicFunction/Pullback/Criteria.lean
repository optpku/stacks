module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MeromorphicFunction.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.WeaklyAssociatedPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.CodimensionZero
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

/-!
# Criteria for pullbacks of meromorphic functions on algebraic spaces

Pullbacks of meromorphic sections are defined when weakly associated points map to
codimension-zero points, or when the morphism is flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Pullbacks of meromorphic sections are defined for a morphism of algebraic spaces
whose weakly associated source points map to codimension-zero target points. -/
@[stacks 0EN9]
theorem pullbacksMeromorphicFunctionsDefined_of_weakAss_mapsTo_codimZero
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hweak : Set.MapsTo (Points.map f) X.weakAss (codimZeroPoints Y)) :
    PullbacksMeromorphicFunctionsDefined f :=
  sorry

/-- Pullbacks of meromorphic sections are defined for a flat morphism of algebraic
spaces. -/
@[stacks 0EN9]
instance instPullbacksMeromorphicFunctionsDefined_of_flat
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} [Flat f] :
    PullbacksMeromorphicFunctionsDefined f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
