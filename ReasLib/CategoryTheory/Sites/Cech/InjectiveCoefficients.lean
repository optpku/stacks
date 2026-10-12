/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.DeltaFunctor
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.Cech.FixedTarget

variable {C : Type u} [Category.{v} C] {U : C} {I : Type w}
variable (family : I → Over U) [HasIteratedFiberProducts family]
variable [HasProducts.{w} AddCommGrpCat.{max u v}]
variable (ℐ : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) [Injective ℐ]

/-- An injective additive presheaf has vanishing fixed-target Čech cohomology in every positive degree. -/
theorem cechCohomology_isZero_of_injective_pos
    (p : ℕ) (hp : 0 < p) :
    IsZero (cohomology family ℐ p) := sorry

end CategoryTheory.Cech.FixedTarget

end
