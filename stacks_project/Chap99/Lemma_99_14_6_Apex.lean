/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Polarized.Algebraic

/-!
# Yoneda 2-fibre product of polarized proper schemes

The concrete fibre construction remains publicly available from its mathematical owner.
-/

open CategoryTheory CategoryTheory.Limits

universe u

#check (AlgebraicGeometry.Polarized.twoFibreProduct :
  AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids
      (⊤_ AlgebraicGeometry.Scheme.{u}) →
    AlgebraicGeometry.GroupoidsOver (⊤_ AlgebraicGeometry.Scheme.{u}))
