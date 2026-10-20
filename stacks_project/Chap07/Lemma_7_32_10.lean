/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Topos.Point.Properties

/-!
# Canonical recall for Lemma 7.32.10

The direct-image properties of a topos point are reusable independently of
the Chapter 7 presentation, so their canonical owners are in ReasLib.
-/

@[expose] public section

open CategoryTheory

/- Lemma 7.32.10 (05UY): a topos point's direct image preserves limits,
finite limits, and coequalizers; is faithful; sends surjections to locally
surjective maps; and reflects injections, surjections, and isomorphisms. -/

@[stacks 05UY "(1)"] #check @MorphismOfTopoiIn.typePushforward_isRightAdjoint
#check @Limits.PreservesLimits.preservesFiniteLimits
@[stacks 05UY "(2)"] #check @MorphismOfTopoiIn.typePushforward_faithful
@[stacks 05UY "(3)"] #check @MorphismOfTopoiIn.typePushforward_map_isLocallySurjective
@[stacks 05UY "(4)"] #check @MorphismOfTopoiIn.typePushforward_preservesCoequalizers
@[stacks 05UY "(5)"] #check @MorphismOfTopoiIn.typePushforward_reflectsInjective
@[stacks 05UY "(6)"] #check @MorphismOfTopoiIn.typePushforward_reflectsSurjective
@[stacks 05UY "(7)"] #check @MorphismOfTopoiIn.typePushforward_reflectsIsomorphisms
