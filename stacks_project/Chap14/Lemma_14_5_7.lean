/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Split
import StacksCheckRecall

/-!
@stack 016O
-/

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
variable (U : CosimplicialObject C) {n : ℕ} (i : Fin (n + 2))

/- Lemma 14.5.7: every coface morphism of a cosimplicial object is a split monomorphism. -/
@[stacks 016O]
#check (CosimplicialObject.δ.splitMono U i : SplitMono (U.δ i))

#check (inferInstance : IsSplitMono (U.δ i))
#check (inferInstance : Mono (U.δ i))
