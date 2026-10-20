/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Stalks.Filtered
import StacksCheckRecall

@[expose] public section

/- Lemma 6.13.1 (1): the stalk of a category-valued presheaf exists using only the filtered
colimit over open neighborhoods of the point. -/
@[stacks 007H "stalk as a filtered neighborhood colimit"]
recall TopCat.Presheaf.filteredStalk

/- Lemma 6.13.1 (2): for a faithful functor to sets that preserves filtered colimits, the
underlying set of the category-valued stalk is canonically isomorphic to the stalk of the
underlying set-valued presheaf. -/
@[stacks 007H "underlying sets of stalks agree with set-valued stalks"]
recall TopCat.Presheaf.filteredStalkCompIso

/- Lemma 6.13.1 (3): taking the filtered neighborhood colimit defines a functor from
category-valued presheaves to the coefficient category. -/
@[stacks 007H "stalks as filtered neighborhood colimits form a functor"]
recall TopCat.Presheaf.filteredStalkFunctor
