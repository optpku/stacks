/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Associativity
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoricalPullback

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable {D : Type u₄} [Category.{v₄} D]
variable {E : Type u₅} [Category.{v₅} E]
variable (F : A ⥤ B) (G : C ⥤ B) (H : C ⥤ D) (I : E ⥤ D)

/- Lemma 4.31.8: the two iterated categorical pullbacks associated to a four-legged zigzag are
canonically equivalent. The reusable owner is `CategoricalPullback.associativity`. -/
@[stacks 02XC]
#check (CategoryTheory.Limits.CategoricalPullback.associativity F G H I :
  (((CategoricalPullback.π₂ F G) ⋙ H) ⊡ I) ≌
    (F ⊡ ((CategoricalPullback.π₁ H I) ⋙ G)))
