/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef

-- Representable localization is owned by ReasLib, independently of Chapter 7.
public import ReasLib.CategoryTheory.Sites.Localization.Representable
import StacksCheckRecall

@[expose] public section

/- Lemma 7.25.4 (00Y1): sheaves on the localized slice site at `U` are equivalent to objects
over `J.sheafifiedRepresentable U`. -/
#check @CategoryTheory.GrothendieckTopology.RepresentableLocalization.comparison

@[stacks 00Y1] #check @CategoryTheory.GrothendieckTopology.RepresentableLocalization.comparison.isEquivalence
