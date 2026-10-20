module

public import stacks_project.Chap59.Definition_59_18_1

import ReasLib.CategoryTheory.Sites.Cech.InjectiveCoefficients
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.Cech.FixedTarget

variable {C : Type u} [Category.{v} C] {U : C} {I : Type w}
variable (family : I → Over U) [HasIteratedFiberProducts family]
variable [HasProducts.{w} AddCommGrpCat.{max u v}]
variable (ℐ : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) [Injective ℐ]

/- Lemma 59.18.7: for an injective abelian presheaf `ℐ`, positive-degree Čech cohomology for the fixed-target family vanishes. -/
@[stacks 03OR] #check (CategoryTheory.Cech.FixedTarget.cechCohomology_isZero_of_injective_pos :
  ∀ {C : Type u} [Category.{v} C] {U : C} {I : Type w}
    (family : I → Over U) [HasIteratedFiberProducts family]
    [HasProducts.{w} AddCommGrpCat.{max u v}]
    (ℐ : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) [Injective ℐ]
    (p : ℕ),
    0 < p → IsZero (cechCohomology family ℐ p))

end CategoryTheory.Cech.FixedTarget

end
