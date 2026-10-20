/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtered.SpanCocones
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

universe v u

variable {I : Type u} [Category.{v} I] [HasSpanCocones I]

/- Lemma 4.19.6: a category with span cocones is empty or is canonically a nonempty disjoint
union of connected categories that again have span cocones. -/
@[stacks 09WS "connected-component decomposition preserving span cocones"]
#check (HasSpanCocones.emptyOrNonemptyComponents (I := I) :
  IsEmpty I ∨ Nonempty (ConnectedComponents I) ∧
    ∀ j : ConnectedComponents I, IsConnected j.Component ∧ HasSpanCocones j.Component)

end CategoryTheory
