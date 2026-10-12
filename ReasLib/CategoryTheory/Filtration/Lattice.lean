/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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

/-- Definition 12.19.1 (1): an indexed filtration is exhaustive exactly when the supremum of
its stages is the top subobject.  This formulation works for every indexing preorder whenever
`Subobject A` is a complete lattice. -/
theorem isExhaustive_iff_iSup_eq_top [CompleteLattice (Subobject A)]
    (F : IndexedFiltration I A) :
    IsExhaustive F ↔ (⨆ i : I, F.stage i) = ⊤ := sorry

section ZeroObject

variable [HasZeroObject C]

/-- Definition 12.19.1 (2): an indexed filtration is separated exactly when the infimum of its
stages is the bottom subobject.  This formulation works for every indexing preorder whenever
`Subobject A` is a complete lattice. -/
theorem isSeparated_iff_iInf_eq_bot [CompleteLattice (Subobject A)]
    (F : IndexedFiltration I A) :
    IsSeparated F ↔ (⨅ i : I, F.stage i) = ⊥ := sorry

end ZeroObject

end IndexedFiltration

end CategoryTheory
