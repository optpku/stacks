/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.DeltaFunctor
public import ReasLib.CategoryTheory.Sites.Cech.FixedTarget
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.Cech.FixedTarget

variable {C : Type u} [Category.{v} C] {U : C} {I : Type w}
variable (family : I → Over U) [HasIteratedFiberProducts family]
variable [HasProducts.{w} AddCommGrpCat.{max u v}]
variable (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v})

/- Definition 59.18.1 (1): for a fixed-target family with all iterated fibre products, the
Čech complex of an abelian presheaf is the cochain complex attached to the family. -/
@[stacks 03OL] #check (CategoryTheory.Cech.FixedTarget.cechComplex :
  ∀ {C : Type u} [Category.{v} C] {U : C} {I : Type w}
    (family : I → Over U) [HasIteratedFiberProducts family]
    [HasProducts.{w} AddCommGrpCat.{max u v}]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}),
    CochainComplex AddCommGrpCat.{max u v} ℕ)

/- Definition 59.18.1 (2): the degree-`p` Čech cohomology object is the homology of the
Čech complex in degree `p`. -/
@[stacks 03OL] #check (CategoryTheory.Cech.FixedTarget.cohomology :
  ∀ {C : Type u} [Category.{v} C] {U : C} {I : Type w}
    [HasProducts.{w} AddCommGrpCat.{max u v}]
    (family : I → Over U) [HasIteratedFiberProducts family]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (p : ℕ),
    AddCommGrpCat.{max u v})

/-- Compatibility name for the fixed-target Čech cohomology object used by chapter consumers. -/
abbrev cechCohomology (p : ℕ) : AddCommGrpCat.{max u v} :=
  CategoryTheory.Cech.FixedTarget.cohomology family F p

end CategoryTheory.Cech.FixedTarget

end
