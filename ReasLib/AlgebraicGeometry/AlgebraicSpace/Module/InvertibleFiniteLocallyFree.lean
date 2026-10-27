/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank

/-! # Invertibility and local rank one for algebraic-space modules -/

@[expose] public section

open CategoryTheory.MonoidalCategory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- A finite locally free module of rank one is tensor invertible. -/
instance rankOne_isInvertible {S : Scheme.{u}} {X : AlgebraicSpace S}
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank 1 E] :
    isInvertibleObject E := sorry

/-- A tensor-invertible module is finite locally free of rank one. -/
instance instIsFiniteLocallyFreeOfRank_one_of_isInvertibleObject
    {S : Scheme.{u}} {X : AlgebraicSpace S} (L : X.Modules) [isInvertibleObject L] :
    SheafOfModules.IsFiniteLocallyFreeOfRank 1 L := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
