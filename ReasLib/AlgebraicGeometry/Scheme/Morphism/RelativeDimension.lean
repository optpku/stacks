/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension
public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.Topology.KrullDimension.Equidimensional

/-!
# Relative dimensions of scheme morphisms

This leaf packages pointwise upper fibre-dimension bounds and the usual
constant-relative-dimension condition for locally finite-type scheme
morphisms.
-/

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism has relative dimension at most `d` at `x` when the local
dimension of its fibre at `x` is at most `d`. -/
def RelativeDimensionLEAt {X S : Scheme.{u}}
    (f : X ⟶ S) (d : ℕ) (x : X) : Prop :=
  f.fiberDimensionAt x ≤ (d : WithBot ℕ∞)

/-- Unfold the pointwise relative-dimension bound. -/
theorem relativeDimensionLEAt_iff {X S : Scheme.{u}}
    (f : X ⟶ S) (d : ℕ) (x : X) :
    RelativeDimensionLEAt f d x ↔
      f.fiberDimensionAt x ≤ (d : WithBot ℕ∞) := sorry

/-- The pointwise relative-dimension bound is definitionally the local fibre
dimension inequality. -/
theorem relativeDimensionLEAt_def {X S : Scheme.{u}}
    (f : X ⟶ S) (d : ℕ) (x : X) :
    RelativeDimensionLEAt f d x =
      (f.fiberDimensionAt x ≤ (d : WithBot ℕ∞)) := sorry

/-- A locally finite-type morphism has relative dimension at most `d` when its
fibre dimension is at most `d` at every source point. -/
class RelativeDimensionLE {X S : Scheme.{u}}
    (f : X ⟶ S) (d : ℕ) : Prop extends LocallyOfFiniteType f where
  /-- The fibre-dimension bound at a source point. -/
  relativeDimensionLEAt (x : X) : RelativeDimensionLEAt f d x

/-- Characterize relative dimension at most `d` by local finite type and the
pointwise fibre-dimension bounds. -/
theorem relativeDimensionLE_iff {X S : Scheme.{u}}
    (f : X ⟶ S) (d : ℕ) :
    RelativeDimensionLE f d ↔
      LocallyOfFiniteType f ∧ ∀ x : X, RelativeDimensionLEAt f d x := sorry

/-- Characterize relative dimension at most `d` directly through
`fiberDimensionAt`. -/
theorem relativeDimensionLE_iff_fiberDimensionAt_le {X S : Scheme.{u}}
    (f : X ⟶ S) (d : ℕ) :
    RelativeDimensionLE f d ↔
      LocallyOfFiniteType f ∧
        ∀ x : X, f.fiberDimensionAt x ≤ (d : WithBot ℕ∞) := sorry

/-- A relative-dimension bound supplies local finite type. -/
theorem locallyOfFiniteType_of_relativeDimensionLE {X S : Scheme.{u}}
    (f : X ⟶ S) (d : ℕ) [RelativeDimensionLE f d] :
    LocallyOfFiniteType f := sorry

/-- A global relative-dimension bound gives the corresponding bound at a
chosen source point. -/
theorem relativeDimensionLEAt_of_relativeDimensionLE {X S : Scheme.{u}}
    (f : X ⟶ S) (d : ℕ) [RelativeDimensionLE f d] (x : X) :
    RelativeDimensionLEAt f d x := sorry

/-- A global relative-dimension bound gives the local fibre-dimension
inequality at a chosen source point. -/
theorem fiberDimensionAt_le_of_relativeDimensionLE {X S : Scheme.{u}}
    (f : X ⟶ S) (d : ℕ) [RelativeDimensionLE f d] (x : X) :
    f.fiberDimensionAt x ≤ (d : WithBot ℕ∞) := sorry

/-- Every point of a morphism of relative dimension at most `d` belongs to its
fibre-dimension-at-most-`d` locus. -/
theorem mem_fiberDimensionLELocus_of_relativeDimensionLE {X S : Scheme.{u}}
    (f : X ⟶ S) (d : ℕ) [RelativeDimensionLE f d] (x : X) :
    x ∈ f.fiberDimensionLELocus d := sorry

/-- A locally finite-type morphism has relative dimension `d` when every
nonempty fibre is equidimensional of topological Krull dimension `d`. -/
class RelativeDimension {X S : Scheme.{u}}
    (f : X ⟶ S) (d : ℕ) : Prop extends LocallyOfFiniteType f where
  /-- Every nonempty fibre is equidimensional. -/
  equidimensionalSpace_fiber (s : S) (h_nonempty : Nonempty (f.fiber s)) :
    EquidimensionalSpace (f.fiber s)
  /-- Every nonempty fibre has the prescribed topological Krull dimension. -/
  topologicalKrullDim_fiber (s : S) (h_nonempty : Nonempty (f.fiber s)) :
    topologicalKrullDim (f.fiber s) = d

/-- Characterize relative dimension `d` by local finite type and the two
fibrewise conditions. -/
theorem relativeDimension_iff {X S : Scheme.{u}}
    (f : X ⟶ S) (d : ℕ) :
    RelativeDimension f d ↔
      LocallyOfFiniteType f ∧
        (∀ (s : S) (_ : Nonempty (f.fiber s)), EquidimensionalSpace (f.fiber s)) ∧
        ∀ (s : S) (_ : Nonempty (f.fiber s)), topologicalKrullDim (f.fiber s) = d := sorry

/-- A relative-dimension structure supplies local finite type. -/
theorem locallyOfFiniteType_of_relativeDimension {X S : Scheme.{u}}
    (f : X ⟶ S) (d : ℕ) [RelativeDimension f d] :
    LocallyOfFiniteType f := sorry

/-- Every nonempty fibre of a morphism of relative dimension `d` is
equidimensional. -/
theorem equidimensionalSpace_fiber_of_relativeDimension {X S : Scheme.{u}}
    (f : X ⟶ S) (d : ℕ) [h : RelativeDimension f d]
    (s : S) (hs : Nonempty (f.fiber s)) :
    EquidimensionalSpace (f.fiber s) := sorry

/-- Every nonempty fibre of a morphism of relative dimension `d` has
topological Krull dimension `d`. -/
theorem topologicalKrullDim_fiber_eq_of_relativeDimension {X S : Scheme.{u}}
    (f : X ⟶ S) (d : ℕ) [h : RelativeDimension f d]
    (s : S) (hs : Nonempty (f.fiber s)) :
    topologicalKrullDim (f.fiber s) = d := sorry

end AlgebraicGeometry.Scheme.Hom
