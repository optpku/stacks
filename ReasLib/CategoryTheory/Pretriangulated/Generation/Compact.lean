/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Preadditive.CompactObject
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Orthogonal
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Compact Generation

Compact generation is an existential wrapper around the generic compact-object
and weak-generation owners.  The companion equivalences expose both an
unbundled compact generating family and a family in the compact full
subcategory.
-/

open CategoryTheory
open CategoryTheory.Limits

universe w v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroMorphisms D] [HasShift D ℤ]

/-- A family generates if and only if its coproduct is a weak generator. -/
theorem isWeakGenerator_coproduct_iff_isGeneratingFamily {I : Type w} (E : I → D)
    [HasCoproduct E] :
    IsWeakGenerator (∐ E) ↔ IsGeneratingFamily E := sorry

end

section

/-- A category is compactly generated when it has a family of compact generators indexed
in its morphism universe. This predicate does not require a choice of coproducts.
When small coproducts exist, `isWeakGenerator_coproduct_iff_isGeneratingFamily` recovers
the coproduct formulation. -/
@[stacks 09SQ]
def IsCompactlyGenerated (D : Type u) [Category.{v} D] [Preadditive D]
    [HasShift D ℤ] : Prop :=
  ∃ (I : Type v) (E : I → D),
    (∀ i, IsCompactObject (E i)) ∧ IsGeneratingFamily E

variable (D : Type u) [Category.{v} D] [Preadditive D] [HasShift D ℤ]

/-- Compact generation is equivalent to the existence of a compact generating family. -/
theorem isCompactlyGenerated_iff_exists_compact_generatingFamily :
    IsCompactlyGenerated D ↔
      ∃ (I : Type v) (E : I → D),
        (∀ i, IsCompactObject (E i)) ∧ IsGeneratingFamily E := Iff.rfl

/-- Compact generation is equivalent to a generating family valued in the compact full
subcategory. -/
theorem isCompactlyGenerated_iff_exists_compactSubcategory_generatingFamily :
    IsCompactlyGenerated D ↔
      ∃ (I : Type v) (E : I → compactObjectSubcategory D),
        IsGeneratingFamily (fun i ↦ (E i).obj) := by
  constructor
  · rintro ⟨I, E, hcompact, hgen⟩
    exact ⟨I, fun i ↦ ⟨E i, hcompact i⟩, hgen⟩
  · rintro ⟨I, E, hgen⟩
    exact ⟨I, fun i ↦ (E i).obj, fun i ↦ (E i).property, hgen⟩

end

end CategoryTheory
