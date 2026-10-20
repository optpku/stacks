/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Picard
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Picard

/-! # Picard groups of algebraic spaces -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

universe u

/- Invertible modules represent equal Picard classes exactly when they are isomorphic. -/
#check (AlgebraicGeometry.AlgebraicSpace.picardClass_eq_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    (L N : X.Modules) [isInvertibleObject L] [isInvertibleObject N],
    AlgebraicGeometry.AlgebraicSpace.Modules.picardClass L =
      AlgebraicGeometry.AlgebraicSpace.Modules.picardClass N ↔ Nonempty (L ≅ N))
