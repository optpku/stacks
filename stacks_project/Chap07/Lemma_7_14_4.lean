/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.MorphismOfSites

import StacksCheckRecall

@[expose] public section

/-!
[stacks 03CB]

Lemma 7.14.4 is the composition law for morphisms of sites; the intermediate topology remains
an explicit parameter of the canonical API.
-/

#check CategoryTheory.Functor.isContinuous_comp
#check CategoryTheory.RepresentablyFlat.comp
@[stacks 03CB] #check CategoryTheory.IsMorphismOfSites.comp
