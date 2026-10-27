/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.Diagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Separation

/-!
# Separatedness of the relative-Hom functor
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

variable {S : Scheme.{u}} {Y B X : AlgebraicSpace S}

/-- The relative-Hom functor `mor y x` is separated over `B` when `y` is flat,
proper, and of finite presentation and `x` is separated and of finite presentation. -/
instance instIsSeparatedOver (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x] :
    Quot.IsSeparatedOver (mor y x) := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
