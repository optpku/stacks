/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.ChangeOfIndex
import StacksCheckRecall

@[expose] public section

universe vI uI vJ uJ vC uC

namespace CategoryTheory.Limits

variable {I : Type uI} [Category.{vI} I]
variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]
variable {H : I ⥤ J}
variable {M : I ⥤ C} [HasLimit M]
variable {N : J ⥤ C} [HasLimit N]
variable (t : H ⋙ N ⟶ M)

/- Lemma 4.14.9: a transformation `H ⋙ N ⟶ M` induces a unique comparison
`limit N ⟶ limit M` with the prescribed projection composites. -/
@[stacks 002L]
#check (limitComparison.existsUnique t :
  ∃! θ : limit N ⟶ limit M,
    ∀ i : I, θ ≫ limit.π M i = limit.π N (H.obj i) ≫ t.app i)

end CategoryTheory.Limits
