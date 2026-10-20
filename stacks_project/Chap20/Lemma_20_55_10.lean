/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Eta.Derived.FiniteFree
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.RingedSpace

/- Lemma 20.55.10 (0GTA) (1): for a locally principal regular ideal, the derived eta functor
preserves finite freeness of each cohomology stalk. -/
@[stacks 0GTA "(1)"]
#check @IdealSheaf.Eta.Derived.cohomologyStalkFiniteFree

/- Lemma 20.55.10 (0GTA) (2): over a nonzero stalk ring, the finite-free cohomology stalk has
the same rank after applying the derived eta functor. -/
@[stacks 0GTA "(2)"]
#check @IdealSheaf.Eta.Derived.cohomologyStalk_rank_eq

@[stacks 0GTA "structural stalk form"]
#check @IdealSheaf.Eta.Derived.cohomologyStalk_isomorphic

@[stacks 0GTA "stalkwise tensor-power formula"]
#check @IdealSheaf.Eta.Derived.cohomologyStalk_isomorphic_tensorPower

#check @IdealSheaf.Eta.Derived.tensorPower_torsionQuotient_isomorphic_cohomology
#check @IdealSheaf.Eta.Derived.cohomologyStalk_finrank_eq
#check @IdealSheaf.IsTorsionFreeAt
#check @IdealSheaf.IsRegularPrincipal.isTorsionFreeAt_of_finiteFree
#check @InvertiblePower.stalk_freeRankOne
#check @CategoryTheory.ModuleCat.freeRankOne.finiteFree_tensorRight_iff
#check @CategoryTheory.ModuleCat.freeRankOne.rank_tensorRight_eq
