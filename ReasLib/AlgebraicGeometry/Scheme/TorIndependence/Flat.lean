/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.TorIndependence

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.TorIndependentOver

/-- A scheme flat over the base is Tor independent over that base from every other scheme. -/
theorem of_flat_left {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [Flat f] :
    TorIndependentOver (Over.mk f) (Over.mk g) := sorry

end AlgebraicGeometry.Scheme.TorIndependentOver
