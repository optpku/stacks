/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef

-- The slice-product right-adjoint comparison is independent of sites and sheaves.
public import ReasLib.CategoryTheory.Limits.OverPost
import StacksCheckRecall

@[expose] public section

/- Lemma 7.28.2 (03EF): a binary-product-preserving functor induces the canonical comparison
between the right adjoints in its localized slice-product square. This is owned by the generic
`TwoSquare.overPost` API in ReasLib. -/
@[stacks 03EF] #check @CategoryTheory.TwoSquare.overPost.rightAdjointIso

#check @CategoryTheory.TwoSquare.overPost.rightAdjointIsoApp
#check @CategoryTheory.TwoSquare.overPost.rightAdjointIso_hom_app_isIso
