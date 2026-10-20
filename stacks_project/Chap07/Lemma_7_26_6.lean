/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.AbsoluteGlueing
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.26.6

The reusable absolute-glueing category and reconstruction equivalence are
owned by `ReasLib.CategoryTheory.Sites.Descent.AbsoluteGlueing`.
-/

@[expose] public section

/- Lemma 7.26.6 (0GWK): sheaves on a site are equivalent to absolute glueing data formed from
sheaves on its slice sites. -/
@[stacks 0GWK] #check @CategoryTheory.GrothendieckTopology.AbsoluteGlueing
#check @CategoryTheory.GrothendieckTopology.AbsoluteGlueing.FromSheaf.functor
#check @CategoryTheory.GrothendieckTopology.AbsoluteGlueing.ToSheaf.functor
#check @CategoryTheory.GrothendieckTopology.AbsoluteGlueing.FromSheaf.functorIsEquivalence
#check @CategoryTheory.GrothendieckTopology.AbsoluteGlueing.sheafEquivalence
