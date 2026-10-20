module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalences restricted to full subcategories

An ambient equivalence restricts to an equivalence when the target object property pulls back
to the source object property.  This is the proposition-level bridge from the canonical
`restrict` functor to `Equivalence.congrFullSubcategory`.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ObjectProperty.FullSubcategory.restrict

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {P : ObjectProperty C} {Q : ObjectProperty D}

/-- Restricting an equivalence to an isomorphism-invariant target property gives an equivalence
of the corresponding full subcategories. -/
@[stacks 001D "equivalences restricted to invariant full subcategories"]
theorem isEquivalence_of_inverseImage_eq (F : C ⥤ D) [F.IsEquivalence]
    [Q.IsClosedUnderIsomorphisms] (h : Q.inverseImage F = P) :
    (restrict F (le_of_eq h.symm)).IsEquivalence := sorry

end CategoryTheory.ObjectProperty.FullSubcategory.restrict
