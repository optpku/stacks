/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose

/-!
# Lemma 7.44.2

The coefficient-functor comparisons are owned by the acyclic ReasLib pullback
leaf.  The source statement for underlying sets is the specialization
`F := forget A`; the generic owner also serves all other coefficient functors.
-/

@[expose] public section

/- Lemma 7.44.2 (00YT) (1): presheaf inverse and direct image are the canonical
Kan-extension/precomposition adjunction, and a coefficient functor preserving
left Kan extensions commutes with the inverse-image construction. -/
@[stacks 00YT "(1)"] #check @CategoryTheory.Functor.lanAdjunction

@[stacks 00YT "(1)"] #check @CategoryTheory.Functor.lanCompIsoOfPreserves

/- Lemma 7.44.2 (00YT) (2): direct image on sheaves is the canonical right
adjoint and commutes with coefficient postcomposition. -/
@[stacks 00YT "(2)"] #check @CategoryTheory.Functor.sheafAdjunctionContinuous

@[stacks 00YT "(2)"] #check @CategoryTheory.Functor.sheafPushforwardContinuous.compSheafCompose

/- Lemma 7.44.2 (00YT) (3): the constructed and abstract inverse-image
functors commute with coefficient postcomposition under the canonical
Kan-extension and sheafification hypotheses. -/
@[stacks 00YT "(3)"] #check @CategoryTheory.Functor.sheafPullbackConstruction.compSheafComposeIso

@[stacks 00YT "(3)"] #check @CategoryTheory.Functor.sheafPullback.compSheafComposeIso
