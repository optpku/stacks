module

public import ReasLib.CategoryTheory.Bicategory.StrictCostructuredArrow.Basic

/-!
# Source projection for strict costructured arrows

This module packages the source-object, source-map, and source-cell readouts
as the canonical pseudofunctor to the source bicategory.
-/

@[expose] public section

universe wA vA uA wC vC uC

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace Bicategory

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {C : Type uC} [Bicategory.{wC, vC} C]

namespace StrictCostructuredArrow

variable [Bicategory.Strict A] [Bicategory.Strict C]
variable {K : StrictPseudofunctor A C} {X : C}

variable (K X) in
/-- The canonical projection from strict costructured arrows to their source bicategory.

It forgets the structural arrow and the strict commutativity witnesses while
retaining source objects, maps, and `2`-cells. -/
def fst : Pseudofunctor (StrictCostructuredArrow K X) A :=
  (LocallyInducedBicategory.forget
      (ColaxCostructuredArrow K.toPseudofunctor X)
      (fun S : StrictCostructuredArrow K X ↦ Implementation.toColax S)
      (Implementation.strictHomProperty K X)).toPseudofunctor.comp
    (ColaxComma.fst K.toPseudofunctor
      (Pseudofunctor.const (LocallyDiscrete (Discrete PUnit.{1})) X))

/-- The source projection returns the left object of a strict costructured arrow. -/
@[simp]
theorem fst_obj (S : StrictCostructuredArrow K X) :
    (fst K X).obj S = S.left := sorry

/-- The source projection returns the source map of a strict costructured-arrow morphism. -/
@[simp]
theorem fst_map {S T : StrictCostructuredArrow K X} (f : S ⟶ T) :
    (fst K X).map f = map f := sorry

/-- The source projection returns the source cell of a strict costructured-arrow `2`-morphism. -/
@[simp]
theorem fst_map₂ {S T : StrictCostructuredArrow K X} {f g : S ⟶ T} (η : f ⟶ g) :
    (fst K X).map₂ η = map₂ η := sorry

end StrictCostructuredArrow

end Bicategory

end CategoryTheory
