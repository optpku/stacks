/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef

public import ReasLib.CategoryTheory.Sites.Localization.SheafHom
import StacksCheckRecall

@[expose] public section

/- 0D7X (Lemma 7.26.3): the sheaf-Hom from the sheafified representable of `U` to `F` is
isomorphic to the pushforward of the restriction `F.over U` from the localized site. -/
@[stacks 0D7X] #check @CategoryTheory.Sheaf.HomRepresentable.isomorphic_pushforwardRestriction
