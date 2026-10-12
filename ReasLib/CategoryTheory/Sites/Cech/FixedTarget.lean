/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.Basic
public import ReasLib.CategoryTheory.Sites.Cech.FreeAbelian

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.Cech.FixedTarget

variable {C : Type u} [Category.{v} C] {U : C} {I : Type w}
variable (family : I → Over U) [HasIteratedFiberProducts family]
variable [HasProducts.{w} AddCommGrpCat.{max u v}]
variable (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v})

/-- The object-level Čech cochain complex of a fixed-target family and an additive presheaf. -/
abbrev cechComplex : CochainComplex AddCommGrpCat.{max u v} ℕ :=
  (FormalCoproduct.cochainComplexFunctor (familyCech family)).obj
    ((restrictPresheafToOver U).obj F)

end CategoryTheory.Cech.FixedTarget

end
