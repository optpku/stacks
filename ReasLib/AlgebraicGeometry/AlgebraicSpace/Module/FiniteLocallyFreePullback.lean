/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank

/-! # Preservation of prescribed finite local rank under pullback -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Pullback of modules preserves finite local freeness of a prescribed rank. -/
instance pullback_isFiniteLocallyFreeOfRank (g : Y ⟶ X) (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E] :
    SheafOfModules.IsFiniteLocallyFreeOfRank r ((pullback g).obj E) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

