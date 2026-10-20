module

public import Mathlib.Topology.Semicontinuity.Defs
public import Mathlib.Topology.LocallyConstant.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber.ConnectedComponents
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Fiber.GeometricallyReduced

/-!
# Semicontinuity and local constancy of geometric fibre-component counts

The geometric fibre-component count of a proper, flat morphism of finite
presentation of algebraic spaces is lower semicontinuous on the target.
When the geometric fibres are reduced, this count is locally constant.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Topology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The geometric fibre-component count of a proper, flat morphism of finite
presentation of algebraic spaces is lower semicontinuous on the target. -/
theorem lowerSemicontinuous_geometricFiberComponentCount {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f] :
    LowerSemicontinuous (geometricFiberComponentCount f) :=
  sorry

/-- The geometric fibre-component count of a proper, flat morphism of finite
presentation of algebraic spaces with reduced geometric fibres is locally
constant on the target. -/
theorem isLocallyConstant_geometricFiberComponentCount {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f]
    (h_reduced : geometricallyReducedFiberLocus f = Set.univ) :
    IsLocallyConstant (geometricFiberComponentCount f) :=
  sorry

/-- The geometric fibre-component count of a proper, flat, finite-presentation
morphism of algebraic spaces with reduced geometric fibres is locally constant
at a point of the target. -/
theorem eventually_eq_geometricFiberComponentCount {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f]
    (h_reduced : geometricallyReducedFiberLocus f = Set.univ) (y : Points Y) :
    ∀ᶠ y' in 𝓝 y, geometricFiberComponentCount f y' = geometricFiberComponentCount f y :=
  (isLocallyConstant_geometricFiberComponentCount f h_reduced).eventually_eq y

end AlgebraicGeometry.AlgebraicSpace
