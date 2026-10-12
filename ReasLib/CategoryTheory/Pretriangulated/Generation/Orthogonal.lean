/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Weak Generation by Shifts

The definitions here only require a category with zero morphisms and an integer
shift.  They are stated through Mathlib's `ObjectProperty.shiftClosure` and
orthogonal owners, so later triangulated arguments can use the same API.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroMorphisms D] [HasShift D ℤ]

/-- A family generates when the right orthogonal of all of its shifts contains only zero
objects. -/
@[stacks 09SJ "generating family in a category with shifts"]
def IsGeneratingFamily {I : Type*} (E : I → D) : Prop :=
  ((ofObj E).shiftClosure ℤ).rightOrthogonal = IsZero

/-- An object is a weak generator when every nonzero object receives a nonzero morphism from
some shift of it. -/
@[stacks 09SJ]
def IsWeakGenerator (E : D) : Prop :=
  ∀ ⦃K : D⦄, ¬ IsZero K → ∃ (n : ℤ) (f : E ⟶ K⟦n⟧), f ≠ 0

/-- Weak generation is equivalent to the vanishing of the right orthogonal of the shift closure
of the singleton object property. -/
theorem isWeakGenerator_iff_rightOrthogonal_shifts_eq_isZero (E : D) :
    IsWeakGenerator E ↔ ((singleton E).shiftClosure ℤ).rightOrthogonal = IsZero := sorry

/-- An object is a weak generator precisely when the corresponding singleton-indexed family is
generating. -/
theorem isWeakGenerator_iff_isGeneratingFamily_unit (E : D) :
    IsWeakGenerator E ↔ IsGeneratingFamily (fun _ : Unit ↦ E) := sorry

end

end CategoryTheory
