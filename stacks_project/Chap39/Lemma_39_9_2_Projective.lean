/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety.Projective

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

#check
  (AlgebraicGeometry.AbelianVariety.instProjective :
    ∀ {k : Type u} [Field k] (A : SchemeOverField k) [GrpObj A] [AbelianVariety A],
      Projective A.hom)
