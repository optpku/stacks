/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.Exact
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

/- Lemma 59.18.2 (Tag 03OM): the fixed-target Cech cochain functor is exact on additive
presheaves. -/
@[stacks 03OM] #check
  (CategoryTheory.Cech.FixedTarget.cochainFunctor_exact :
    ∀ {C : Type u} [Category.{v} C] {U : C} {ι : Type w} (family : ι → Over U)
      [HasIteratedFiberProducts family] [HasProducts.{w} AddCommGrpCat.{max u v}],
      exactFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})
        (CochainComplex AddCommGrpCat.{max u v} ℕ)
        (CategoryTheory.Cech.FixedTarget.cochainFunctor family))

end
