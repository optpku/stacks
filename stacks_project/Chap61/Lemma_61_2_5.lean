/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.ConnectedComponents.Pullback
import StacksCheckRecall

/-!
# Lemma 61.2.5

A cartesian pullback of a spectral space along a map from a profinite space
into its connected-components quotient remains spectral, and recovers the
profinite space as its connected-components quotient. If the original space
is w-local, so is the pullback, the projection is w-local, and closed points
are reflected.
-/

@[expose] public section

open Set

universe u v w

namespace ConnectedComponents

variable {X : Type u} {T : Type v}
  [TopologicalSpace X] [TopologicalSpace T]
  [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
  {f : C(T, ConnectedComponents X)}

/- Lemma 61.2.5 (1): a cartesian cone over the connected-components quotient of a
spectral space with profinite base-change space has a spectral vertex. -/
@[stacks 096C] #check (ConnectedComponents.pullback.spectralSpace_of_isHomeomorph :
  ∀ [SpectralSpace X] {Y : Type w} [TopologicalSpace Y] {g : Y → X} {p : C(Y, T)}
    (hcomm : ∀ y, mk (g y) = f (p y)),
    IsHomeomorph (pullback.comparison hcomm) → SpectralSpace Y)

/- Lemma 61.2.5 (2): the connected-components lift of the profinite projection
from the cartesian vertex identifies its connected-components quotient with T. -/
@[stacks 096C] #check
  (ConnectedComponents.pullback.isHomeomorph_connectedComponentsLift_of_isHomeomorph :
    ∀ [SpectralSpace X] {Y : Type w} [TopologicalSpace Y] {g : Y → X} {p : C(Y, T)}
      (hcomm : ∀ y, mk (g y) = f (p y)),
      IsHomeomorph (pullback.comparison hcomm) →
        IsHomeomorph p.continuous.connectedComponentsLift)

/- Lemma 61.2.5 (3): if X is W-local, the cartesian vertex is W-local. -/
@[stacks 096C] #check (ConnectedComponents.pullback.wLocalSpace_of_isHomeomorph :
  ∀ [WLocalSpace X] {Y : Type w} [TopologicalSpace Y] {g : Y → X} {p : C(Y, T)}
    (hcomm : ∀ y, mk (g y) = f (p y)),
    IsHomeomorph (pullback.comparison hcomm) → WLocalSpace Y)

/- Lemma 61.2.5 (4): if X is W-local, the cartesian projection to X is W-local. -/
@[stacks 096C] #check (ConnectedComponents.pullback.isWLocalMap_of_isHomeomorph :
  ∀ [WLocalSpace X] {Y : Type w} [TopologicalSpace Y] {g : Y → X} {p : C(Y, T)}
    (hcomm : ∀ y, mk (g y) = f (p y))
    (he : IsHomeomorph (pullback.comparison hcomm)),
    let wLocalY : WLocalSpace Y := pullback.wLocalSpace_of_isHomeomorph hcomm he
    IsWLocalMap g)

/- Lemma 61.2.5 (5): if X is W-local, the closed points of the cartesian vertex
are the preimage of the closed points of X. -/
@[stacks 096C] #check (ConnectedComponents.pullback.closedPoints_eq_preimage_of_isHomeomorph :
  ∀ [WLocalSpace X] {Y : Type w} [TopologicalSpace Y] {g : Y → X} {p : C(Y, T)}
    (hcomm : ∀ y, mk (g y) = f (p y)),
    IsHomeomorph (pullback.comparison hcomm) → closedPoints Y = g ⁻¹' closedPoints X)

end ConnectedComponents
