/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.GeometricallyReduced

universe u

open CategoryTheory

#check (AlgebraicGeometry.Scheme.Hom.geometricallyReducedFiberLocus :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}}, (f : X ⟶ Y) → Set Y)
