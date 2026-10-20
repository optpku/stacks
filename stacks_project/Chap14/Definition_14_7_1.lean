/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import ReasLib.CategoryTheory.Limits.FunctorCategory.Pointwise.Pullback
import StacksCheckRecall

/-!
@stack 016T
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SimplexCategory Simplicial
open scoped Simplicial

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]
variable {U V W : SimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
variable [Limits.FunctorCategory.HasPointwisePullback a b]
variable {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))

/- Definition 14.7.1 (1): the fibre product is the canonical functor-category pullback, and
evaluation identifies it with the degreewise pullback. -/
#check (Limits.FunctorCategory.pointwise.pullback a b : HasPullback a b)

@[stacks 016T "Definition 14.7.1 (1)"]
#check (Limits.FunctorCategory.evaluation.pullbackIso a b (op ⦋n⦌) :
  (pullback a b) _⦋n⦌ ≅ pullback (a.app (op ⦋n⦌)) (b.app (op ⦋n⦌)))

/- Definition 14.7.1 (2): every face map is the canonical map of the corresponding degreewise
pullbacks. -/
@[stacks 016T "Definition 14.7.1 (2)"]
#check (Limits.FunctorCategory.evaluation.pullbackIso.map
    a b (SimplexCategory.δ i).op :
  (pullback a b).δ i ≫
      (Limits.FunctorCategory.evaluation.pullbackIso a b (op ⦋n⦌)).hom =
    (Limits.FunctorCategory.evaluation.pullbackIso a b (op ⦋n + 1⦌)).hom ≫
      Limits.FunctorCategory.evaluation.pullbackMap a b (SimplexCategory.δ i).op)

#check Limits.FunctorCategory.evaluation.pullbackMap.fst a b (SimplexCategory.δ i).op
#check Limits.FunctorCategory.evaluation.pullbackMap.snd a b (SimplexCategory.δ i).op

/- Definition 14.7.1 (3): every degeneracy map is the canonical map of the corresponding
degreewise pullbacks. -/
@[stacks 016T "Definition 14.7.1 (3)"]
#check (Limits.FunctorCategory.evaluation.pullbackIso.map
    a b (SimplexCategory.σ j).op :
  (pullback a b).σ j ≫
      (Limits.FunctorCategory.evaluation.pullbackIso a b (op ⦋n + 1⦌)).hom =
    (Limits.FunctorCategory.evaluation.pullbackIso a b (op ⦋n⦌)).hom ≫
      Limits.FunctorCategory.evaluation.pullbackMap a b (SimplexCategory.σ j).op)

end CategoryTheory.SimplicialObject
