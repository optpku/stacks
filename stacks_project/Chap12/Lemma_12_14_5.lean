/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.DegreewiseSplit.ChainHomology
import StacksCheckRecall

@[expose] public section

open CategoryTheory ComplexShape HomologicalComplex

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex (ChainComplex C ℤ)}
variable (hS : S.ShortExact)
variable (σ : ∀ n : ℤ, (S.degreewise n).Splitting) (i : ℤ)

/- Lemma 12.14.5: the shifted homology map induced by the degreewise-split chain connecting
morphism is the boundary in the long exact homology sequence. -/
@[stacks 011E]
#check (CategoryTheory.ShortComplex.ShortExact.DegreewiseSplit.Chain.boundary_eq_δ hS σ i :
  (HomologicalComplex.homologyFunctor C (down ℤ) 0).shiftMap
      (ChainComplex.homOfDegreewiseSplit S σ) i (i - 1) (neg_add_eq_sub 1 i) =
    hS.δ i (i - 1) (down_mk i (i - 1) (sub_add_cancel i 1)))
