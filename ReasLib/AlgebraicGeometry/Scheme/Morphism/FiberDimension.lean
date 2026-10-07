module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Stalk
public import ReasLib.RingTheory.KrullDimension.Relative

/-!
# Local dimensions of fibres of scheme morphisms

This leaf defines the local dimension of a scheme-theoretic fibre at a source
point through the relative dimension of the corresponding stalk map.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The local dimension of the fibre of `f` at `x`, computed from the relative
dimension of the stalk map at its closed point. -/
noncomputable def fiberDimensionAt {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) : WithBot ℕ∞ :=
  relativeDimensionAtWith (S.presheaf.stalk (f x)) (X.presheaf.stalk x)
    (f.stalkAlgebra x)
    (IsLocalRing.closedPoint (X.presheaf.stalk x))

/-- Expand `fiberDimensionAt` as the relative dimension for the algebra induced by the stalk
map. -/
theorem fiberDimensionAt_eq_relativeDimensionAt {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) :
    f.fiberDimensionAt x =
      relativeDimensionAtWith (S.presheaf.stalk (f x)) (X.presheaf.stalk x)
        (f.stalkAlgebra x)
        (IsLocalRing.closedPoint (X.presheaf.stalk x)) := sorry

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
