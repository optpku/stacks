/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Flat
public import ReasLib.CategoryTheory.Sites.MorphismOfSites.Exactness
import StacksCheckRecall

/-!
# Lemma 18.31.2

The two exactness assertions live at their natural categorical owners: inverse image of abelian
sheaves for a morphism of sites, and module pullback for a flat morphism of ringed sites.
-/

@[expose] public section

/- Lemma 18.31.2 (1) (04JC): inverse image on abelian sheaves is exact. -/
@[stacks 04JC "(1)"]
#check @CategoryTheory.Functor.IsMorphismOfSites.abelianPullback_exact

/- Lemma 18.31.2 (2) (04JC): flat module pullback is exact. -/
@[stacks 04JC "(2)"]
#check @RingedSite.Hom.IsFlat.pullback_exact
