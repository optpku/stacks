/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.FixedTarget
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe w v u

/- Remark 59.18.9: all preceding statements concern presheaves, and the common
   fixed-target Čech construction below requires no Grothendieck topology. -/
@[stacks 03OT] #check
  (CategoryTheory.Cech.FixedTarget.cechComplex :
    ∀ {C : Type u} [CategoryTheory.Category.{v} C] {U : C} {I : Type w}
      (family : I → CategoryTheory.Over U)
      [CategoryTheory.HasIteratedFiberProducts family]
      [CategoryTheory.Limits.HasProducts.{w} AddCommGrpCat.{max u v}]
      (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}),
      CochainComplex AddCommGrpCat.{max u v} ℕ)
