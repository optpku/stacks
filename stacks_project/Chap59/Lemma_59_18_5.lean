/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Definition_59_18_1
public import ReasLib.CategoryTheory.Sites.Cech.FreeAbelian.Comparison
import StacksCheckRecall
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Cech.FreeAbelian Opposite

universe w v u

namespace CategoryTheory.Cech.FixedTarget

variable {C : Type u} [Category.{v} C] {U : C} {I : Type w}
variable (family : I → Over U) [HasIteratedFiberProducts family]
variable [HasProducts.{w} AddCommGrpCat.{max u v}]
variable [HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})]
variable (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v})

/- Lemma 59.18.5: the Čech cochain complex is canonically identified with the cochain
complex represented by the alternating complex of free-abelian representables of the cover. -/
@[stacks 03OP] #check
  (CategoryTheory.Cech.FreeAbelian.comparisonAppIso family F :
    (CategoryTheory.Cech.FreeAbelian.homFunctor family).obj F ≅
      CategoryTheory.Cech.FixedTarget.cechComplex family F)

end CategoryTheory.Cech.FixedTarget

end
