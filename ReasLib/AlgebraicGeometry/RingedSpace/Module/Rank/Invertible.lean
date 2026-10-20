/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Rank.Invertible
public import ReasLib.AlgebraicGeometry.RingedSpace.LocallyRinged
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Invertible
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
import Mathlib.Tactic.CrossRefAttribute

/-!
# Rank-one and invertible modules on ringed spaces

This leaf specializes the ringed-site rank-one API to topological ringed spaces. The foundational
invertible-module owner remains independent of rank and local-ring hypotheses.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- An invertible module sheaf is finite locally free of rank one when all stalk rings are
local. -/
@[stacks 0B8M "converse"]
theorem rankOne_of_isInvertible
    (L : RingedSpace.Modules X) [isInvertibleObject L]
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    SheafOfModules.IsFiniteLocallyFreeOfRank 1 L := sorry

/-- On a ringed space with local stalk rings, finite local freeness of rank one is equivalent to
tensor invertibility. -/
@[stacks 0B8M "equivalence"]
theorem rankOne_iff_isInvertible
    (L : RingedSpace.Modules X)
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    SheafOfModules.IsFiniteLocallyFreeOfRank 1 L ↔ isInvertibleObject L := sorry

/-- The right-tensor convention for invertibility yields the same rank-one conclusion on a
ringed space with local stalk rings. -/
theorem rankOne_of_tensorRightEquivalence
    (L : RingedSpace.Modules X) [Functor.IsEquivalence (tensorRight L)]
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    SheafOfModules.IsFiniteLocallyFreeOfRank 1 L := sorry

end AlgebraicGeometry.RingedSpace
