/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.Cleavage
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Fibered
import Mathlib.Tactic.CrossRefAttribute

/-!
# The selected cleavage of a fibred pseudo-pullback

This leaf names the instance-driven cleavage used by `Functor.Chosen` on an explicit
pseudo-pullback. Keeping this choice in one owner ensures that reindexing comparisons use the
same fibredness witness as the selected fiber pseudofunctor.
-/

@[expose] public section

universe u v w vT

namespace CategoryTheory.FiberedCategoryOver.PseudoPullback

variable {C : Type u} [Category.{v} C]
variable {X Y S : FiberedCategoryOver.{u, v, w, vT} C}

/-- The cleavage selected from the canonical fibredness instance of an explicit
pseudo-pullback. This is the shared choice boundary for its `Functor.Chosen` reindexing API. -/
@[stacks 0040 "selected cleavage of an explicit pseudo-pullback"]
noncomputable def chosenCleavage (F : X ⟶ S) (G : Y ⟶ S)
    [h_fibered : (BasedCategory.PseudoPullback
      (toBasedFunctor F) (toBasedFunctor G)).p.IsFibered] :
    (BasedCategory.PseudoPullback
      (toBasedFunctor F) (toBasedFunctor G)).p.Cleavage :=
  Functor.Cleavage.ofIsFibered
    (BasedCategory.PseudoPullback
      (toBasedFunctor F) (toBasedFunctor G)).p

end CategoryTheory.FiberedCategoryOver.PseudoPullback
