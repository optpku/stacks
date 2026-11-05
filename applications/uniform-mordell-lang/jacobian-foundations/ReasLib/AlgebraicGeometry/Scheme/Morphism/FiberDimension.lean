module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Stalk
public import ReasLib.RingTheory.KrullDimension.Relative

/-!
# Local dimensions of fibres of scheme morphisms

The local dimension of a scheme-theoretic fibre at a source point is the local
topological Krull dimension at the corresponding point of that fibre.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The local topological Krull dimension of the fibre of `f` at `x`. -/
noncomputable def fiberDimensionAt {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) : WithBot ℕ∞ :=
  topologicalKrullDimAt (f.asFiber x)

/-- The local dimension of a fibre at a source point equals the local topological Krull
dimension at the corresponding point of the scheme-theoretic fibre. -/
theorem fiberDimensionAt_eq_topologicalKrullDimAt_asFiber {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) :
    f.fiberDimensionAt x = topologicalKrullDimAt (f.asFiber x) := sorry

/-- The locus where the local dimension of the fibre of `f` is at most `n`. -/
noncomputable def fiberDimensionLELocus {X S : Scheme.{u}}
    (f : X ⟶ S) (n : ℕ) : Set X :=
  {x | f.fiberDimensionAt x ≤ (n : WithBot ℕ∞)}

/-- Membership in the fibre-dimension locus is exactly the corresponding local
dimension bound. -/
theorem mem_fiberDimensionLELocus {X S : Scheme.{u}}
    (f : X ⟶ S) (n : ℕ) (x : X) :
    x ∈ f.fiberDimensionLELocus n ↔
      f.fiberDimensionAt x ≤ (n : WithBot ℕ∞) := sorry

end AlgebraicGeometry.Scheme.Hom
