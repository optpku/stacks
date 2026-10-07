module

public import ReasLib.Topology.WLocal
import StacksCheckRecall

@[expose] public section

universe u v

/- Definition 61.2.3 (1): a spectral space is w-local if the set of closed points is
closed and every point specializes to a unique closed point. -/
@[stacks 096A] #check (WLocalSpace : ∀ (X : Type u) [TopologicalSpace X], Prop)

#check (WLocalSpace.iff_of_spectral : ∀ {X : Type u}
  [TopologicalSpace X] [SpectralSpace X], WLocalSpace X ↔
  IsClosed (closedPoints X) ∧ ∀ x : X, ∃! y ∈ closedPoints X, x ⤳ y)

/- Definition 61.2.3 (2): a continuous map of w-local spaces is w-local if it is
spectral and sends closed points to closed points. -/
@[stacks 096A] #check (IsWLocalMap : ∀ {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y] [WLocalSpace X] [WLocalSpace Y],
  (X → Y) → Prop)

#check (IsWLocalMap.spec : ∀ {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y] [WLocalSpace X] [WLocalSpace Y]
  (f : X → Y), IsWLocalMap f ↔
  IsSpectralMap f ∧ Set.MapsTo f (closedPoints X) (closedPoints Y))
