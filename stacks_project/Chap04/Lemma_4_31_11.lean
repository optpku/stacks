module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Bilimit
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoricalPullback

universe v u

variable {A : Type (max u v)} [Category.{v} A]
variable {B : Type (max u v)} [Category.{v} B]
variable {S : Type (max u v)} [Category.{v} S]
variable {X : Type (max u v)} [Category.{v} X]
variable (G₁ : A ⥤ S) (G₂ : B ⥤ S)
variable (P : CategoricalPullback.CatCommSqOver
  (G₁.prod G₂) (Functor.diag S) X)
variable [P.IsBilimit]

/- Lemma 4.31.11: the canonical comparison from a `2`-fibre-product square in the symmetric
diagonal presentation to the ordinary categorical pullback is an equivalence. -/
@[stacks 02XE]
#check (CategoricalPullback.CatCommSqOver.Symmetric.comparison.isEquivalence G₁ G₂ P :
  (CategoricalPullback.CatCommSqOver.Symmetric.comparison G₁ G₂ P).IsEquivalence)
