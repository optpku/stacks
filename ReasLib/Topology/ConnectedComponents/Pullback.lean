/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.Homeomorph.Defs
public import ReasLib.Topology.ConnectedComponents.Profinite
public import ReasLib.Topology.Spectral.Product
public import ReasLib.Topology.Spectral.Subspace
public import ReasLib.Topology.WLocal

/-!
# Connected-components pullbacks

Pullbacks of the connected-components quotient along maps from profinite spaces
are spectral. Their components are identified with the profinite factor, and
W-locality and closed points are preserved by the projection.
-/

@[expose] public section

open Set

universe u v w

namespace ConnectedComponents

variable {X : Type u} {T : Type v} [TopologicalSpace X] [TopologicalSpace T]

/-- The cartesian pullback of the connected-components quotient along a continuous
map, realized as a subspace of the product. -/
abbrev pullback (f : C(T, ConnectedComponents X)) : Type (max u v) :=
  {point : X × T // mk point.1 = f point.2}

variable {f : C(T, ConnectedComponents X)}

/-- The projection of the connected-components pullback to the original space. -/
def pullback.fst : pullback f → X := fun point ↦ point.1.1

/-- The projection of the connected-components pullback to the base-change space. -/
def pullback.snd : pullback f → T := fun point ↦ point.1.2

/-- The defining square of the connected-components pullback commutes. -/
theorem pullback.mk_fst_eq (point : pullback f) :
    mk (pullback.fst point) = f (pullback.snd point) :=
  sorry

/-- The projection of the connected-components pullback to the original space is
continuous. -/
theorem pullback.continuous_fst : Continuous (pullback.fst : pullback f → X) :=
  sorry

/-- The projection of the connected-components pullback to the base-change space
is continuous. -/
theorem pullback.continuous_snd : Continuous (pullback.snd : pullback f → T) :=
  sorry

/-- The comparison map sends a commutative cone to the connected-components
pullback. -/
def pullback.comparison {Y : Type w} [TopologicalSpace Y] {g : Y → X} {p : Y → T}
    (hcomm : ∀ y, mk (g y) = f (p y)) : Y → pullback f :=
  fun y ↦ ⟨(g y, p y), hcomm y⟩

/-- The first projection of the comparison map is the cone map to the original
space. -/
theorem pullback.comparison_fst {Y : Type w} [TopologicalSpace Y] {g : Y → X} {p : Y → T}
    (hcomm : ∀ y, mk (g y) = f (p y)) (y : Y) :
    pullback.fst (pullback.comparison hcomm y) = g y :=
  sorry

/-- The second projection of the comparison map is the cone map to the base-change
space. -/
theorem pullback.comparison_snd {Y : Type w} [TopologicalSpace Y] {g : Y → X} {p : Y → T}
    (hcomm : ∀ y, mk (g y) = f (p y)) (y : Y) :
    pullback.snd (pullback.comparison hcomm y) = p y :=
  sorry

/-- The connected-components pullback of a spectral space is closed in the
product. -/
theorem pullback.isClosed [SpectralSpace X] :
    IsClosed {point : X × T | mk point.1 = f point.2} :=
  sorry

variable [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]

/-- The connected-components pullback of a spectral space along a map from a
profinite space is spectral. -/
instance pullback.instSpectralSpace [SpectralSpace X] : SpectralSpace (pullback f) :=
  sorry

/-- The connected-components quotient of the pullback of a spectral space along
a map from a profinite space is homeomorphic to that profinite space via the
lift of the second projection. -/
theorem pullback.isHomeomorph_connectedComponentsLift [SpectralSpace X] :
    IsHomeomorph
      (pullback.continuous_snd.connectedComponentsLift :
        ConnectedComponents (pullback f) → T) :=
  sorry

/-- The connected-components pullback of a W-local space along a map from a
profinite space is W-local. -/
instance pullback.instWLocalSpace [WLocalSpace X] : WLocalSpace (pullback f) :=
  sorry

/-- The first projection from a connected-components pullback of a W-local space
along a map from a profinite space is W-local. -/
instance pullback.instIsWLocalMap_fst [WLocalSpace X] :
    IsWLocalMap (pullback.fst : pullback f → X) :=
  sorry

/-- The closed points of a connected-components pullback of a W-local space along
a map from a profinite space are the preimage of the original closed points. -/
theorem pullback.closedPoints_eq_preimage_fst [WLocalSpace X] :
    closedPoints (pullback f) = pullback.fst ⁻¹' closedPoints X :=
  sorry

variable {Y : Type w} [TopologicalSpace Y] {g : Y → X} {p : C(Y, T)}

namespace pullback

/-- A cartesian cone over the connected-components quotient of a spectral space
with profinite base-change space has a spectral vertex. -/
theorem spectralSpace_of_isHomeomorph [SpectralSpace X]
    (hcomm : ∀ y, mk (g y) = f (p y))
    (he : IsHomeomorph (pullback.comparison hcomm)) : SpectralSpace Y :=
  sorry

/-- The lift of the profinite projection from a cartesian cone over the
connected-components quotient of a spectral space is a homeomorphism. -/
theorem isHomeomorph_connectedComponentsLift_of_isHomeomorph [SpectralSpace X]
    (hcomm : ∀ y, mk (g y) = f (p y))
    (he : IsHomeomorph (pullback.comparison hcomm)) :
    IsHomeomorph p.continuous.connectedComponentsLift :=
  sorry

/-- A cartesian cone over the connected-components quotient of a W-local space
with profinite base-change space has a W-local vertex. -/
theorem wLocalSpace_of_isHomeomorph [WLocalSpace X]
    (hcomm : ∀ y, mk (g y) = f (p y))
    (he : IsHomeomorph (pullback.comparison hcomm)) : WLocalSpace Y :=
  sorry

/-- The projection to a W-local space from a cartesian cone over its
connected-components quotient with profinite base-change space is W-local. -/
theorem isWLocalMap_of_isHomeomorph [WLocalSpace X]
    (hcomm : ∀ y, mk (g y) = f (p y))
    (he : IsHomeomorph (pullback.comparison hcomm)) :
    let wLocalY : WLocalSpace Y := pullback.wLocalSpace_of_isHomeomorph hcomm he
    IsWLocalMap g :=
  sorry

/-- The closed points of the vertex of a cartesian cone over the
connected-components quotient of a W-local space with profinite base-change
space are the preimage of its closed points under the cone projection. -/
theorem closedPoints_eq_preimage_of_isHomeomorph [WLocalSpace X]
    (hcomm : ∀ y, mk (g y) = f (p y))
    (he : IsHomeomorph (pullback.comparison hcomm)) :
    closedPoints Y = g ⁻¹' closedPoints X :=
  sorry

end pullback

end ConnectedComponents
