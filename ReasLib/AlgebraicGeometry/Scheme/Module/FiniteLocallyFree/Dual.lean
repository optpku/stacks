/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank

/-!
# Duals of finite locally free scheme modules

The internal-Hom dual of a finite locally free module on a scheme is finite locally free.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree

/-- The internal-Hom dual of a finite locally free module on a scheme is finite locally free. -/
noncomputable instance dual {X : Scheme.{u}} (E : X.Modules)
    [E.IsFiniteLocallyFree] : (Scheme.Modules.dual E).IsFiniteLocallyFree := sorry

end AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree

namespace AlgebraicGeometry.Scheme.Modules

/-- The dual of a finite locally free module of rank `r` is finite locally free of rank `r`. -/
instance instIsFiniteLocallyFreeOfRankDual {X : Scheme.{u}} (E : X.Modules) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r E] :
    IsFiniteLocallyFreeOfRank r (dual E) := sorry

end AlgebraicGeometry.Scheme.Modules
