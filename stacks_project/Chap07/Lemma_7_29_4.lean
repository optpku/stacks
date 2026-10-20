/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.DenseSubsite.Surjective
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.29.4 recall

The locally-surjective site of a sheaf subcategory and its dense-subsite
comparison belong to ReasLib. This source file retains the labeled recall.
-/

@[expose] public section

/- Lemma 7.29.4 (03A1): a full subcategory of sheaves admits the
locally-surjective topology and its sheafified-representable dense-subsite
comparison. -/
@[stacks 03A1] #check @CategoryTheory.ObjectProperty.SurjectiveSite.topology

@[stacks 03A1] #check @CategoryTheory.ObjectProperty.SurjectiveSite.topology_subcanonical

@[stacks 03A1] #check @CategoryTheory.ObjectProperty.SurjectiveSite.RepresentableFunctor.isSpecialCocontinuous

@[stacks 03A1] #check @CategoryTheory.ObjectProperty.SurjectiveSite.RepresentableFunctor.yonedaIso

@[stacks 03A1] #check @CategoryTheory.ObjectProperty.SurjectiveSite.RepresentableFunctor.sheafifiedRepresentableIso
