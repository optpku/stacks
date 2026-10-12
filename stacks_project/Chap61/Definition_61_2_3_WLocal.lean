/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.WLocal

@[expose] public section

universe u v

#check (WLocalSpace : ∀ (X : Type u) [TopologicalSpace X], Prop)

#check (IsWLocalMap : ∀ {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y] [WLocalSpace X] [WLocalSpace Y],
  (X → Y) → Prop)

#check (WLocalSpace.iff_of_spectral : ∀ {X : Type u}
  [TopologicalSpace X] [SpectralSpace X], WLocalSpace X ↔
  IsClosed (closedPoints X) ∧ ∀ x : X, ∃! y ∈ closedPoints X, x ⤳ y)

#check (IsWLocalMap.spec : ∀ {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y] [WLocalSpace X] [WLocalSpace Y]
  (f : X → Y), IsWLocalMap f ↔
  IsSpectralMap f ∧ Set.MapsTo f (closedPoints X) (closedPoints Y))
