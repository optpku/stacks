/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber.ConnectedComponents

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.30.1: The geometric fibre-component count at a point is the count
at its chosen geometric representative. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.geometricFiberComponentCount_apply :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y),
      geometricFiberComponentCount f y =
        geometricFiberComponentCountAt f (geometricPointOver y))
