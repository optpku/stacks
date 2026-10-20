/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.SplitEqualizer
import StacksCheckRecall

universe v u

/- Lemma 35.4.18: the diagram
`S^[0] ⟶ S^[1] ⇉ S^[2]` with arrows `S.δ 1`, `S.δ 2`, and `S.δ 1`
is a split equalizer, canonically split by `S.σ 0`. -/
@[stacks 08X3] #check
  (@CategoryTheory.CosimplicialObject.SplitEqualizer.splitting :
    {C : Type u} → [CategoryTheory.Category.{v} C] →
      (S : CategoryTheory.CosimplicialObject C) →
        CategoryTheory.IsSplitEqualizer
          (S.δ (2 : Fin 3)) (S.δ (1 : Fin 3)) (S.δ (1 : Fin 2)))
