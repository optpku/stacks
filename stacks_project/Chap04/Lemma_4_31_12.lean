/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.DiagonalModels.Bilimit
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe v u

variable {C : Type (max u v)} [Category.{v} C]
variable {S : Type (max u v)} [Category.{v} S]
variable {G₁ G₂ : C ⥤ S}
variable {C' : Type (max u v)} [Category.{v} C']
variable (P : CategoricalPullback.CatCommSqOver
  (G₁.prod' G₂) (Functor.diag S) C')
variable [P.IsBilimit]

/- Lemma 4.31.12: the specified comparison from a diagonal `2`-fibre-product square to the
corresponding iterated categorical-pullback model is an equivalence. -/
@[stacks 02XF]
#check (CategoricalPullback.CatCommSqOver.iteratedDiagonalComparison.isEquivalence P :
  P.iteratedDiagonalComparison.IsEquivalence)
