module

public import Mathlib.AlgebraicGeometry.Artinian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point
public import ReasLib.Topology.KrullDimension.Local

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme of finite natural topological Krull dimension has a closed, finite-type point
whose local topological Krull dimension equals the global dimension. -/
@[stacks 0DRR]
theorem exists_closedPoint_topologicalKrullDimAt_eq
    (X : Scheme.{u}) {d : ℕ} (hdim : topologicalKrullDim X = d) :
    ∃ x : X, x ∈ closedPoints X ∧ IsFiniteTypePoint x ∧
      topologicalKrullDimAt x = d := sorry

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- In a locally Noetherian scheme, a point has local topological Krull dimension zero exactly
when its singleton is open. -/
theorem topologicalKrullDimAt_eq_zero_iff_isOpen_singleton {x : X} :
    topologicalKrullDimAt x = 0 ↔ IsOpen ({x} : Set X) := sorry

end AlgebraicGeometry.Scheme
