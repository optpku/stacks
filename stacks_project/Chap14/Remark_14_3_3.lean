/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import StacksCheckRecall

/-!
@stack 016C
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe v u

variable {C : Type u} [Category.{v} C]
variable (U : SimplicialObject C)
variable {n : ℕ} {i k : Fin (n + 2)} {j l : Fin (n + 1)}
variable (hik : i ≤ k) (hij : i ≤ j.castSucc) (hji : j.castSucc < i) (hjl : j ≤ l)

/- Remark 14.3.3 (1): abbreviated face maps satisfy the first simplicial identity. -/
@[stacks 016C "Remark 14.3.3 (1)"]
#check (U.δ_comp_δ hik :
  U.δ k.succ ≫ U.δ i = U.δ i.castSucc ≫ U.δ k)

#check (U.δ i : U _⦋n + 1⦌ ⟶ U _⦋n⦌)
#check (U.σ j : U _⦋n⦌ ⟶ U _⦋n + 1⦌)

/- Remark 14.3.3 (2): a face before a later degeneracy satisfies the second identity. -/
@[stacks 016C "Remark 14.3.3 (2)"]
#check (U.δ_comp_σ_of_le hij :
  U.σ j.succ ≫ U.δ i.castSucc = U.δ i ≫ U.σ j)

/- Remark 14.3.3 (3): a degeneracy is cancelled by the corresponding face. -/
@[stacks 016C "Remark 14.3.3 (3)"]
#check (U.δ_comp_σ_self (i := j) :
  U.σ j ≫ U.δ j.castSucc = 𝟙 (U _⦋n⦌))

/- Remark 14.3.3 (4): a degeneracy is also cancelled by the succeeding face. -/
@[stacks 016C "Remark 14.3.3 (4)"]
#check (U.δ_comp_σ_succ (i := j) :
  U.σ j ≫ U.δ j.succ = 𝟙 (U _⦋n⦌))

/- Remark 14.3.3 (5): a later face and an earlier degeneracy satisfy the fourth identity. -/
@[stacks 016C "Remark 14.3.3 (5)"]
#check (U.δ_comp_σ_of_gt hji :
  U.σ j.castSucc ≫ U.δ i.succ = U.δ i ≫ U.σ j)

/- Remark 14.3.3 (6): abbreviated degeneracy maps satisfy the final simplicial identity. -/
@[stacks 016C "Remark 14.3.3 (6)"]
#check (U.σ_comp_σ hjl :
  U.σ l ≫ U.σ j.castSucc = U.σ j ≫ U.σ l.succ)
