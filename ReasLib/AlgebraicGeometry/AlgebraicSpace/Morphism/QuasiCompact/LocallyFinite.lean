/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.LocallyCompact
public import ReasLib.Topology.LocallyFinite.Image
public import Mathlib.Topology.Sets.Closeds

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- A quasi-compact morphism of algebraic spaces sends a locally finite family of closed
subsets to a locally finite family of closures of their images in the canonical point spaces. -/
theorem locallyFinite_closure_image {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] {I : Type v} (T : I → Closeds (Points X))
    (hT : LocallyFinite (fun i ↦ (T i : Set (Points X)))) :
    LocallyFinite (fun i ↦ closure (Points.map f '' (T i : Set (Points X)))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
