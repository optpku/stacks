/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LinearSystem.VanishingLocus

open AlgebraicGeometry

universe u

#check (AlgebraicGeometry.LinearSystem.vanishingIdeal :
  ∀ {k : Type u} [Field k]
    (X : SchemeOverField k) (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (n : ℕ) (s : Fin (n + 1) → SchemeOverField.globalSectionsMod X L),
    (AlgebraicGeometry.LinearSystem.product X n).IdealSheafData)
