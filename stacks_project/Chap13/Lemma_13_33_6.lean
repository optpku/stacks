/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Limits.Sequential
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.33.6

The textbook short exact sequence is the abelian specialization of the
neutral sequential-telescope API.  The finite-prefix presentation is useful
outside homotopy-colimit arguments, so it is owned by
`CategoryTheory.Limits.Sequential.FinitePrefix` rather than by this chapter.
-/

#check @CategoryTheory.Limits.Sequential.telescopeMap
#check @CategoryTheory.Limits.Sequential.ι_comp_telescopeMap
#check @CategoryTheory.Limits.Sequential.telescopeMap_comp_sigmaDesc
#check @CategoryTheory.Limits.Sequential.FinitePrefix.obj
#check @CategoryTheory.Limits.Sequential.FinitePrefix.inclusion
#check @CategoryTheory.Limits.Sequential.FinitePrefix.lastι
#check @CategoryTheory.Limits.Sequential.FinitePrefix.stageProjection
#check @CategoryTheory.Limits.Sequential.FinitePrefix.stageMap
#check @CategoryTheory.Limits.Sequential.FinitePrefix.stageRetraction
#check @CategoryTheory.Limits.Sequential.FinitePrefix.stageNatTrans
#check @CategoryTheory.Limits.Sequential.FinitePrefix.toCoproduct
#check @CategoryTheory.Limits.Sequential.FinitePrefix.sourceCocone
#check @CategoryTheory.Limits.Sequential.FinitePrefix.sourceIsColimit
#check @CategoryTheory.Limits.Sequential.FinitePrefix.targetIsColimit
#check @CategoryTheory.Limits.Sequential.FinitePrefix.coconeCompat

@[stacks 093W] #check @CategoryTheory.Limits.Sequential.telescopeMap_shortExact
