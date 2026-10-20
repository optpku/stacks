/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.KrullDimension.Height
import StacksCheckRecall

@[expose] public section

/-! @stack 00KG -/

universe u

section

variable {R : Type u} [CommRing R]

/- Lemma 10.60.4 (1): Krull dimension is the supremum of the heights
of maximal prime ideals. -/
@[stacks 00KG "(1)"]
#check (Ideal.iSup_isMaximal_height_eq_ringKrullDim (R := R) :
  (⨆ (I : Ideal R) (_ : I.IsMaximal), (I.height : WithBot ℕ∞)) =
    ringKrullDim R)

/- Lemma 10.60.4 (2): equivalently, Krull dimension is the supremum
of the heights of all prime ideals. -/
@[stacks 00KG "(2)"]
#check (Ideal.iSup_isPrime_height_eq_ringKrullDim (R := R) :
  (⨆ (I : Ideal R) (_ : I.IsPrime), (I.height : WithBot ℕ∞)) =
    ringKrullDim R)

end
