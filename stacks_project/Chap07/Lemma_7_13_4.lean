/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef

-- The continuous sheafification comparison is generic site-theoretic infrastructure.
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Pullback
import StacksCheckRecall

@[expose] public section

/- Lemma 7.13.4 (00WY): a continuous functor transports the sheafification unit through left
Kan extension to an isomorphism after sheafification. -/
@[stacks 00WY] #check @CategoryTheory.Functor.lanSheafificationIso
