/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.Pushout

/-! # Coefficient pushout of square-zero algebra extensions -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Hom.SquareZeroAlgebraExtension.pushoutFunctor :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢),
    SquareZeroAlgebraExtension f ℱ ⥤ SquareZeroAlgebraExtension f 𝒢)
