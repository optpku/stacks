/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FiniteFree.RankOne
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Rank.Invertible
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fixed-rank module sheaves at stalks

Fixed local rank gives a basis-free categorical description of every stalk.  The rank-one case
is exposed separately because it is the reusable input for tensor calculations.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- The stalk of a finite locally free rank-one module sheaf is a free rank-one module over the
stalk ring, without a chosen basis. -/
@[stacks 01C9 "rank-one stalk", stacks 0GTA "rank-one stalk"]
theorem stalkModuleCat_freeRankOne
    (L : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank 1 L] (x : X) :
    ModuleCat.freeRankOne (X.presheaf.stalk x) (stalkModuleCat L x) := sorry

end AlgebraicGeometry.RingedSpace
