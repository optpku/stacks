/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.Matrix.MinorIdeal.Injective
import StacksCheckRecall

/-!
# Lemma 15.15.6

@stack 00MX
-/

@[expose] public section

/- Lemma 15.15.6, clauses (1) and (2): injectivity is equivalent to full exterior rank and
zero annihilator of the rank-minor ideal. -/
@[stacks 00MX "Lemma 15.15.6, (1) iff (2)"]
#check @LinearMap.RankMinorIdeal.injective_iff_fullRank_and_annihilator_eq_bot

/- Lemma 15.15.6, clauses (1) and (3): in the Noetherian case, injectivity is equivalent to
full exterior rank and the rank-minor ideal being the unit ideal or containing a
nonzerodivisor. -/
@[stacks 00MX "Lemma 15.15.6, (1) iff (3)"]
#check @LinearMap.RankMinorIdeal.injective_iff_fullRank_and_eq_top_or_exists_isRegular

/- Positive depth is the canonical Noetherian companion to the rank-minor criterion. -/
#check @LinearMap.RankMinorIdeal.injective_iff_fullRank_and_one_le_depth

#check @LinearMap.exteriorRank
#check @LinearMap.rankMinorIdeal
