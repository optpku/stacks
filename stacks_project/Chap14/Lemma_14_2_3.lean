/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import StacksCheckRecall

/-!
@stack 0167
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

variable {n : ℕ} {i k : Fin (n + 2)} {j l : Fin (n + 1)}
variable (hik : i ≤ k) (hij : i ≤ j.castSucc) (hji : j.castSucc < i) (hjl : j ≤ l)

/- Lemma 14.2.3 (1): two coface maps satisfy the first simplicial identity. -/
@[stacks 0167 "Lemma 14.2.3 (1)"]
#check (SimplexCategory.δ_comp_δ hik :
  SimplexCategory.δ i ≫ SimplexCategory.δ k.succ =
    SimplexCategory.δ k ≫ SimplexCategory.δ i.castSucc)

/- Lemma 14.2.3 (2): a coface before a later codegeneracy satisfies the second simplicial
identity. -/
@[stacks 0167 "Lemma 14.2.3 (2)"]
#check (SimplexCategory.δ_comp_σ_of_le hij :
  SimplexCategory.δ i.castSucc ≫ SimplexCategory.σ j.succ =
    SimplexCategory.σ j ≫ SimplexCategory.δ i)

/- Lemma 14.2.3 (3): a codegeneracy cancels the corresponding coface. -/
@[stacks 0167 "Lemma 14.2.3 (3)"]
#check (SimplexCategory.δ_comp_σ_self (i := j) :
  SimplexCategory.δ j.castSucc ≫ SimplexCategory.σ j = 𝟙 ⦋n⦌)

/- Lemma 14.2.3 (4): a codegeneracy also cancels the succeeding coface. -/
@[stacks 0167 "Lemma 14.2.3 (4)"]
#check (SimplexCategory.δ_comp_σ_succ (i := j) :
  SimplexCategory.δ j.succ ≫ SimplexCategory.σ j = 𝟙 ⦋n⦌)

/- Lemma 14.2.3 (5): a later coface and an earlier codegeneracy satisfy the fourth simplicial
identity. -/
@[stacks 0167 "Lemma 14.2.3 (5)"]
#check (SimplexCategory.δ_comp_σ_of_gt hji :
  SimplexCategory.δ i.succ ≫ SimplexCategory.σ j.castSucc =
    SimplexCategory.σ j ≫ SimplexCategory.δ i)

/- Lemma 14.2.3 (6): two codegeneracy maps satisfy the final simplicial identity. -/
@[stacks 0167 "Lemma 14.2.3 (6)"]
#check (SimplexCategory.σ_comp_σ hjl :
  SimplexCategory.σ j.castSucc ≫ SimplexCategory.σ l =
    SimplexCategory.σ l.succ ≫ SimplexCategory.σ j)
