/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.CompactObject.Closure
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Compact
public import Mathlib.CategoryTheory.Triangulated.Generators
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Compact Generators and the Compact Subcategory

This leaf relates weak generation in a compactly generated triangulated
category to classical generation inside its full subcategory of compact
objects.  The ambient generator predicates remain the canonical Mathlib
object-property predicates.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasShift D ℤ] [Preadditive D]
  [HasCoproducts.{max u v} D]

/-- An object weakly generates the compact objects when every nonzero compact object receives a
nonzero morphism from an integer shift of it.  This ambient formulation avoids changing
universes merely to bundle the compact full subcategory. -/
@[stacks 09SS "weak generation of compact objects"]
def IsWeakGeneratorOfCompacts (E : D) : Prop :=
  ∀ ⦃K⦄, IsCompactObject K → ¬ IsZero K →
    ∃ (n : ℤ) (f : E ⟶ K⟦n⟧), f ≠ 0

namespace IsCompactObject

/-- A compact weak generator makes the ambient category compactly generated. -/
@[stacks 09SQ]
theorem isCompactlyGenerated {E : D} (hE : IsCompactObject E)
    (hweak : IsWeakGenerator E) :
    IsCompactlyGenerated D := sorry

end IsCompactObject

end

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
  [HasCoproducts.{max u v} D] [IsTriangulated D]

/-- An object classically generates the compact objects when every compact object lies in its
Mathlib triangulated envelope.  Keeping this relation in the ambient category makes it usable
without a universe lift of the bundled compact full subcategory. -/
@[stacks 09SS "classical generation of compact objects"]
def IsClassicalGeneratorOfCompacts (E : D) : Prop :=
  (IsCompactObject : ObjectProperty D) ≤ (ObjectProperty.singleton E).triangEnvelope

/-- The ambient classical-generation predicate agrees with Mathlib's classical-generator
predicate in the compact full subcategory. -/
theorem isClassicalGeneratorOfCompacts_iff {E : D} (hE : IsCompactObject E) :
    IsClassicalGeneratorOfCompacts E ↔
      (ObjectProperty.singleton
        (⟨E, hE⟩ : compactObjectSubcategory D)).IsClassicalTriangulatedGenerator := sorry

/-- The ambient weak-generation predicate agrees with weak generation inside the compact full
subcategory. -/
theorem isWeakGeneratorOfCompacts_iff {E : D} (hE : IsCompactObject E) :
    IsWeakGeneratorOfCompacts E ↔
      IsWeakGenerator (⟨E, hE⟩ : compactObjectSubcategory D) := sorry

namespace IsCompactObject

/-- A compact weak generator classically generates the compact full subcategory. -/
@[stacks 09SR]
theorem isClassicalTriangulatedGenerator {E : D} (hE : IsCompactObject E)
    (hweak : IsWeakGenerator E) :
    (ObjectProperty.singleton (⟨E, hE⟩ : compactObjectSubcategory D)).IsClassicalTriangulatedGenerator := sorry

/-- Classical generation of the compact full subcategory by a compact object, together with
ambient compact generation, implies weak generation in the ambient category. -/
@[stacks 09SR]
theorem isWeakGenerator {E : D} (hE : IsCompactObject E)
    (hclass :
      (ObjectProperty.singleton (⟨E, hE⟩ : compactObjectSubcategory D)).IsClassicalTriangulatedGenerator)
    (hD : IsCompactlyGenerated D) :
    IsWeakGenerator E := sorry

/-- For a compact object, weak generation is equivalent to classical generation of the compact
full subcategory together with ambient compact generation. -/
@[stacks 09SR]
theorem isWeakGenerator_iff {E : D} (hE : IsCompactObject E) :
    IsWeakGenerator E ↔
      ((ObjectProperty.singleton (⟨E, hE⟩ : compactObjectSubcategory D)).IsClassicalTriangulatedGenerator ∧
        IsCompactlyGenerated D) := sorry

end IsCompactObject

end

end CategoryTheory
