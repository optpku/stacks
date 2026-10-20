/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.H.Comparison

universe u v

#check
  (AlgebraicGeometry.Scheme.HCovering :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v},
      (ι → CategoryTheory.Over T) → Prop)
