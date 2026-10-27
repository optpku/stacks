/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.TorIndependence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

/-! # Tor independence of a flat morphism -/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.TorIndependentOver

/-- A flat morphism is Tor independent of every morphism to the same base. -/
theorem of_flat_left {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y' ⟶ Y) [Flat f] :
    TorIndependentOver (Over.mk f) (Over.mk g) := sorry

end AlgebraicGeometry.AlgebraicSpace.TorIndependentOver
