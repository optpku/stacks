/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Quasi-compactness of morphisms represented by schemes

Quasi-compactness agrees for a scheme morphism and its induced morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of representable algebraic spaces over a scheme is quasi-compact if and
only if the representing morphism of schemes is quasi-compact. -/
theorem quasiCompact_ofOverMap_iff {S : Scheme.{u}} {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    QuasiCompact (ofOverMap f0) ↔ AlgebraicGeometry.QuasiCompact f0.left :=
  sorry

/-- Quasi-compactness of the induced morphism of algebraic spaces implies
quasi-compactness of its representing scheme morphism. -/
instance instQuasiCompact_left_ofOverMap {S : Scheme.{u}} {X0 Y0 : Over S}
    (f0 : X0 ⟶ Y0) [QuasiCompact (ofOverMap f0)] :
    AlgebraicGeometry.QuasiCompact f0.left :=
  (quasiCompact_ofOverMap_iff f0).mp inferInstance

end AlgebraicGeometry.AlgebraicSpace
