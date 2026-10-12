/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Pullback
import StacksCheckRecall

/-!
@stack 0172
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SimplexCategory
open scoped Simplicial

noncomputable section

universe v u

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]
variable {U V W : CosimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
variable [Limits.FunctorCategory.HasPointwisePullback a b]
variable {m n : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌)

/- Definition 14.10.1 (1): the fibre product cosimplicial object is computed degreewise. -/
#check (pointwise.pullback a b : HasPullback a b)

@[stacks 0172 "Definition 14.10.1 (1)"]
#check (Limits.FunctorCategory.evaluation.pullbackIso a b ⦋n⦌ :
  (pullback a b) ^⦋n⦌ ≅ pullback (a.app ⦋n⦌) (b.app ⦋n⦌))

/- Definition 14.10.1 (2): every structure map is the canonical map between the corresponding
degreewise pullbacks. -/
@[stacks 0172 "Definition 14.10.1 (2)"]
#check (Limits.FunctorCategory.evaluation.pullbackIso.map a b φ :
  (pullback a b).map φ ≫
      (Limits.FunctorCategory.evaluation.pullbackIso a b ⦋m⦌).hom =
    (Limits.FunctorCategory.evaluation.pullbackIso a b ⦋n⦌).hom ≫
      Limits.FunctorCategory.evaluation.pullbackMap a b φ)

#check Limits.FunctorCategory.evaluation.pullbackMap.fst a b φ
#check Limits.FunctorCategory.evaluation.pullbackMap.snd a b φ

end CategoryTheory.CosimplicialObject
