/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Family.LocallyBijective
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.10.17 recall

The reusable coverwise-local-bijectivity criterion belongs to ReasLib. This
source file retains only the labeled textbook recall.
-/

@[expose] public section

/- Lemma 7.10.17 (0H6Y): a map of set-valued presheaves that is bijective on
the members of a cover of every object belongs to `J.W`. -/
@[stacks 0H6Y] #check @CategoryTheory.Presheaf.HasCoverByBijective.w

#check @CategoryTheory.Presheaf.HasCoverByBijective.isLocallyInjective
#check @CategoryTheory.Presheaf.HasCoverByBijective.isLocallySurjective
