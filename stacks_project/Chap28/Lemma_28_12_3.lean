/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay.SerreCondition
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/- Lemma 28.12.3: a locally Noetherian scheme `X` is Cohen-Macaulay if and only if it satisfies
Serre's condition `(S_k)` for every natural number `k`. -/
@[stacks 0342] #check
  (AlgebraicGeometry.Scheme.cohenMacaulay_iff_forall_satisfiesSerreConditionS X :
    AlgebraicGeometry.Scheme.CohenMacaulay X ↔
      ∀ k : ℕ, AlgebraicGeometry.Scheme.satisfiesSerreConditionS X k)
