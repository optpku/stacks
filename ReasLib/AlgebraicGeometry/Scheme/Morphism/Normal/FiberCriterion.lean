/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyNoetherianFibers
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Normal

/-!
# A fibre criterion for normal morphisms

This file characterizes normal scheme morphisms with locally Noetherian fibres
by flatness and geometric normality of their fibres.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A scheme morphism with locally Noetherian fibres is normal exactly when it is
flat and its fibres are geometrically normal. -/
theorem normal_iff_flat_and_geometricallyNormal {X Y : Scheme.{u}}
    (f : X ⟶ Y) (h_fibers : LocallyNoetherianFibers f) :
    Normal f ↔ Flat f ∧ geometrically Scheme.isNormal f := sorry

end AlgebraicGeometry
