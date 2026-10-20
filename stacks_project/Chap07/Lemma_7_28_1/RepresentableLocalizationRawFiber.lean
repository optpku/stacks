/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Over.LeftKanExtension

/-!
# Legacy compatibility module for Lemma 7.28.1

The raw-fibre proof implementation was not a reusable API.  The canonical sigma chart and its
fiber chart now live in ReasLib.
-/

@[expose] public section

#check @CategoryTheory.Over.Forget.LeftKanExtension.objIsoSigma.hom_map
#check @CategoryTheory.Over.Forget.LeftKanExtension.fiberIso
#check @CategoryTheory.Over.Forget.LeftKanExtension.fiberIso.hom_heq_snd
