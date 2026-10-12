/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.ObjectProperty.Over.FilteredColimit

/-!
# Finitely presentable objects over a target

This leaf turns finite presentability in the ambient category into
factorization through a selected filtered colimit presentation over a fixed
target.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace CategoryTheory.ObjectProperty.Over

variable {C : Type u} [Category.{u} C] {X : C}

/-- A morphism from a finitely presentable source over `X` factors through one
selected stage of a filtered colimit presentation of `X`. -/
@[stacks 07C3 "finitely presentable over-object factorization"]
theorem exists_hom_of_isFilteredColimit
    (P : ObjectProperty (CategoryTheory.Over X))
    (hfiltered : IsFiltered P.FullSubcategory)
    (hcolimit : IsColimit (forgetCocone P))
    (A : CategoryTheory.Over X) (hA : IsFinitelyPresentable.{u} A.left) :
    ∃ B : P.FullSubcategory, Nonempty (A ⟶ B.obj) := sorry

/-- A selected subcategory gives a filtered colimit presentation exactly when
it is cofinal among a filtered colimit presentation by finitely presentable
test objects. -/
@[stacks 07C3 "finitely presentable selected over-objects"]
theorem isFilteredColimit_iff_factorization
    {P Q : ObjectProperty (CategoryTheory.Over X)}
    (hPQ : P ≤ Q) (hQfiltered : IsFiltered Q.FullSubcategory)
    (hQcolimit : Nonempty (IsColimit (forgetCocone Q)))
    (hQfinite : ∀ A : Q.FullSubcategory, IsFinitelyPresentable.{u} A.obj.left) :
    (IsFiltered P.FullSubcategory ∧ Nonempty (IsColimit (forgetCocone P))) ↔
      ∀ A : Q.FullSubcategory, ∃ B : P.FullSubcategory, Nonempty (A.obj ⟶ B.obj) := sorry

end CategoryTheory.ObjectProperty.Over
