/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowMotive.Tate

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Correspondence
open scoped CategoryTheory.MonoidalCategory

universe u

#check (ChowMotive.Tate.rightInverseIso :
  ∀ (k : Type u) [Field k] (n : ℤ),
    ChowMotive.tateTwist (SchemeOverField.point k) n ⊗
        ChowMotive.tateTwist (SchemeOverField.point k) (-n) ≅
      𝟙_ (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)))
