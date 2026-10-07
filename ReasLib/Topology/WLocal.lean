module

public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.Hom

/-!
# W-local spectral spaces

A spectral space is w-local when its closed points form a closed set and every
point specializes to a unique closed point. A map of w-local spaces is w-local
when it is spectral and sends closed points to closed points.
-/

@[expose] public section

open Set

universe u v w

/-- A spectral space is w-local when the set of closed points is closed and every
point specializes to a unique closed point. -/
@[mk_iff, stacks 096A]
class WLocalSpace (X : Type u) [TopologicalSpace X] : Prop extends SpectralSpace X where
  /-- The set of closed points is a closed subset. -/
  isClosed_closedPoints : IsClosed (closedPoints X)
  /-- Every point specializes to a unique closed point. -/
  existsUnique_specializes_mem_closedPoints :
    ∀ x : X, ∃! y ∈ closedPoints X, x ⤳ y

/-- A `T1` spectral space is w-local: every point is closed, so specialization is
equality. -/
instance instWLocalSpaceOfT1 {X : Type u} [TopologicalSpace X] [SpectralSpace X] [T1Space X] :
    WLocalSpace X := sorry

/-- A continuous map of w-local spaces is w-local when it is spectral and sends
closed points to closed points. -/
@[mk_iff, stacks 096A]
class IsWLocalMap {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [WLocalSpace X] [WLocalSpace Y] (f : X → Y) : Prop where
  /-- A w-local map is spectral. -/
  isSpectralMap : IsSpectralMap f
  /-- A w-local map sends closed points to closed points. -/
  mapsTo_closedPoints : MapsTo f (closedPoints X) (closedPoints Y)

namespace WLocalSpace

/-- The closed-points set of a w-local space is closed, and every point specializes
to a unique closed point. -/
theorem spec {X : Type u} [TopologicalSpace X] [WLocalSpace X] :
    IsClosed (closedPoints X) ∧ ∀ x : X, ∃! y ∈ closedPoints X, x ⤳ y := sorry

/-- A spectral space is w-local if and only if its closed points form a closed set
and every point specializes to a unique closed point. -/
theorem iff_of_spectral {X : Type u} [TopologicalSpace X] [SpectralSpace X] :
    WLocalSpace X ↔
      IsClosed (closedPoints X) ∧ ∀ x : X, ∃! y ∈ closedPoints X, x ⤳ y := sorry

end WLocalSpace

namespace IsWLocalMap

/-- The identity map of a w-local space is w-local. -/
instance id {X : Type u} [TopologicalSpace X] [WLocalSpace X] : IsWLocalMap (id : X → X) where
  isSpectralMap := isSpectralMap_id
  mapsTo_closedPoints := mapsTo_id _

/-- A w-local map is spectral. -/
theorem toIsSpectralMap {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [WLocalSpace X] [WLocalSpace Y]
    (f : X → Y) [IsWLocalMap f] : IsSpectralMap f := sorry

/-- A map of w-local spaces is w-local if and only if it is spectral and sends
closed points to closed points. -/
theorem spec {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [WLocalSpace X] [WLocalSpace Y] (f : X → Y) :
    IsWLocalMap f ↔ IsSpectralMap f ∧ MapsTo f (closedPoints X) (closedPoints Y) := sorry

/-- A w-local map sends the closed points of its source into the closed points of
its target. -/
theorem image_closedPoints_subset {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [WLocalSpace X] [WLocalSpace Y]
    (f : X → Y) [IsWLocalMap f] :
    f '' closedPoints X ⊆ closedPoints Y := sorry

/-- The composite of w-local maps is w-local. -/
theorem comp {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [WLocalSpace X] [WLocalSpace Y] [WLocalSpace Z]
    {f : X → Y} {g : Y → Z} [IsWLocalMap f] [IsWLocalMap g] :
    IsWLocalMap (g ∘ f) := sorry

end IsWLocalMap

namespace IsClosed

/-- A closed subtype of a w-local space is w-local. -/
instance wLocal {X : Type u} [TopologicalSpace X] [WLocalSpace X] {Y : Set X}
    [IsClosed Y] : WLocalSpace Y := sorry

end IsClosed
