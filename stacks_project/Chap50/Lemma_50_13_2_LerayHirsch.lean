/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.LerayHirsch.Absolute

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- This historical module publicly re-exports the absolute Leray-Hirsch API. -/
#check
  (AlgebraicGeometry.Scheme.DeRham.LerayHirsch.fiberSquare_comm :
    ∀ {X Y S : Scheme.{u}} {f : X ⟶ Y} {a : X ⟶ S} {b : Y ⟶ S}
      (sq : CommSq f a b (𝟙 S)) (y : Y),
      f.fiberι y ≫ a =
        f.fiberToSpecResidueField y ≫ (Y.fromSpecResidueField y ≫ b))
