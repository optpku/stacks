module

public import ReasLib.CategoryTheory.Filtration.Exhaustive
public import ReasLib.Order.Filtration
public import Mathlib.Order.CompletePartialOrder

/-!
# Lattice Criteria for Filtrations

This leaf identifies exhaustive and separated indexed filtrations with the corresponding
supremum and infimum conditions in the lattice of subobjects.  The statements are indexed by an
arbitrary preorder; the familiar decreasing `ℤ`-filtration case is a specialization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace IndexedFiltration

variable {I : Type*} [Preorder I] {A : C}

/-- An indexed filtration is exhaustive exactly when the top subobject is the least upper
bound of its stages. -/
theorem isExhaustive_iff_isLUB
    (F : IndexedFiltration I A) :
    IsExhaustive F ↔ IsLUB (Set.range F.stage) ⊤ := sorry

section ZeroObject

variable [HasZeroObject C]

/-- An indexed filtration is separated exactly when the bottom subobject is the greatest lower
bound of its stages. -/
theorem isSeparated_iff_isGLB
    (F : IndexedFiltration I A) :
    IsSeparated F ↔ IsGLB (Set.range F.stage) ⊥ := sorry

end ZeroObject

end IndexedFiltration

end CategoryTheory
