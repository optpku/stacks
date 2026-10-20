/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import ReasLib.CategoryTheory.Limits.FunctorCategory.Pointwise.Pushout
import StacksCheckRecall

/-!
@stack 016W
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SimplexCategory Simplicial
open scoped Simplicial

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]
variable {U V W : SimplicialObject C} (a : U ⟶ V) (b : U ⟶ W)
variable [Limits.FunctorCategory.HasPointwisePushout a b]
variable {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))

/- Definition 14.8.1 (1): the pushout is the canonical functor-category pushout, and evaluation
identifies it with the degreewise pushout. -/
#check (Limits.FunctorCategory.pointwise.pushout a b : HasPushout a b)

@[stacks 016W "Definition 14.8.1 (1)"]
#check (Limits.FunctorCategory.evaluation.pushoutIso a b (op ⦋n⦌) :
  (pushout a b) _⦋n⦌ ≅ pushout (a.app (op ⦋n⦌)) (b.app (op ⦋n⦌)))

/- Definition 14.8.1 (2): every face map is the canonical map of the corresponding degreewise
pushouts. -/
@[stacks 016W "Definition 14.8.1 (2)"]
#check (Limits.FunctorCategory.evaluation.pushoutIso.map
    a b (SimplexCategory.δ i).op :
  (pushout a b).δ i ≫
      (Limits.FunctorCategory.evaluation.pushoutIso a b (op ⦋n⦌)).hom =
    (Limits.FunctorCategory.evaluation.pushoutIso a b (op ⦋n + 1⦌)).hom ≫
      Limits.FunctorCategory.evaluation.pushoutMap a b (SimplexCategory.δ i).op)

#check Limits.FunctorCategory.evaluation.pushoutMap.inl a b (SimplexCategory.δ i).op
#check Limits.FunctorCategory.evaluation.pushoutMap.inr a b (SimplexCategory.δ i).op

/- Definition 14.8.1 (3): every degeneracy map is the canonical map of the corresponding
degreewise pushouts. -/
@[stacks 016W "Definition 14.8.1 (3)"]
#check (Limits.FunctorCategory.evaluation.pushoutIso.map
    a b (SimplexCategory.σ j).op :
  (pushout a b).σ j ≫
      (Limits.FunctorCategory.evaluation.pushoutIso a b (op ⦋n + 1⦌)).hom =
    (Limits.FunctorCategory.evaluation.pushoutIso a b (op ⦋n⦌)).hom ≫
      Limits.FunctorCategory.evaluation.pushoutMap a b (SimplexCategory.σ j).op)

end CategoryTheory.SimplicialObject
