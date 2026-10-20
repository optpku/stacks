/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Spectral.Hom

/-!
# Quasi-compact algebraic spaces and compact points

An algebraic space is quasi-compact if and only if its canonical space of points is compact.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space is quasi-compact if and only if its space of points with the canonical
topology is compact. -/
theorem isQuasiCompact_iff_compactSpace {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsQuasiCompact X ↔ CompactSpace (Points X) := sorry

namespace QuasiCompact

/-- A quasi-compact morphism of algebraic spaces induces a spectral map on their canonical
spaces of points. -/
@[stacks 0EMK]
theorem isSpectralMap {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] : IsSpectralMap (Points.map f) := sorry

/-- The preimage of a compact open subset of the canonical point space under a quasi-compact
morphism of algebraic spaces is compact. -/
theorem isCompact_preimage {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] {V : Set (Points Y)} (hV : IsOpen V) (hVc : IsCompact V) :
    IsCompact (Points.map f ⁻¹' V) := sorry

end QuasiCompact

end AlgebraicGeometry.AlgebraicSpace
