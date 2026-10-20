module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import StacksCheckRecall

/-!
@stack 016L
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe v u

variable {C : Type u} [Category.{v} C]
variable (U : CosimplicialObject C)
variable {n : ℕ} {i k : Fin (n + 2)} {j l : Fin (n + 1)}
variable (hik : i ≤ k) (hij : i ≤ j.castSucc) (hji : j.castSucc < i) (hjl : j ≤ l)

/- Remark 14.5.3 (1): abbreviated coface maps satisfy the first cosimplicial identity. -/
@[stacks 016L "Remark 14.5.3 (1)"]
#check (U.δ_comp_δ hik :
  U.δ i ≫ U.δ k.succ = U.δ k ≫ U.δ i.castSucc)

#check (U.δ i : U ^⦋n⦌ ⟶ U ^⦋n + 1⦌)
#check (U.σ j : U ^⦋n + 1⦌ ⟶ U ^⦋n⦌)

/- Remark 14.5.3 (2): a coface before a later codegeneracy satisfies the second identity. -/
@[stacks 016L "Remark 14.5.3 (2)"]
#check (U.δ_comp_σ_of_le hij :
  U.δ i.castSucc ≫ U.σ j.succ = U.σ j ≫ U.δ i)

/- Remark 14.5.3 (3): a coface is cancelled by the corresponding codegeneracy. -/
@[stacks 016L "Remark 14.5.3 (3)"]
#check (U.δ_comp_σ_self (i := j) :
  U.δ j.castSucc ≫ U.σ j = 𝟙 (U ^⦋n⦌))

/- Remark 14.5.3 (4): the succeeding coface is cancelled by the same codegeneracy. -/
@[stacks 016L "Remark 14.5.3 (4)"]
#check (U.δ_comp_σ_succ (i := j) :
  U.δ j.succ ≫ U.σ j = 𝟙 (U ^⦋n⦌))

/- Remark 14.5.3 (5): a later coface and an earlier codegeneracy satisfy the fourth identity. -/
@[stacks 016L "Remark 14.5.3 (5)"]
#check (U.δ_comp_σ_of_gt hji :
  U.δ i.succ ≫ U.σ j.castSucc = U.σ j ≫ U.δ i)

/- Remark 14.5.3 (6): abbreviated codegeneracy maps satisfy the final cosimplicial identity. -/
@[stacks 016L "Remark 14.5.3 (6)"]
#check (U.σ_comp_σ hjl :
  U.σ j.castSucc ≫ U.σ l = U.σ l.succ ≫ U.σ j)
