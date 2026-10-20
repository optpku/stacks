/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.CompactObject.Generation
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Definition
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Countable Generation by a Compact Object

This leaf isolates the categorical content of the countability criterion for derived categories.
The two object properties below are independent of differential graded presentations: one records
sequential homotopy-colimit presentations, and the other records countability of all shifted
represented Hom types.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

namespace ObjectProperty

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Objects admitting a sequential homotopy-colimit presentation whose stages satisfy `P`.
The presentation is expressed through the intrinsic predicate `HomotopyColimit.IsOf`. -/
@[stacks 0CRM "sequential homotopy-colimit closure"]
def sequentialHomotopyColimits (P : ObjectProperty D) : ObjectProperty D := fun X ↦
  ∃ K : ℕ ⥤ D, (∀ n : ℕ, P (K.obj n)) ∧ HomotopyColimit.IsOf K X

end

section

variable {D : Type u} [Category.{v} D] [HasShift D ℤ]

/-- Objects whose shifted Hom types represented by `G` are all countable. -/
@[stacks 0CRM "countable shifted represented Hom types"]
def countableShiftedHomFrom (G : D) : ObjectProperty D := fun X ↦
  ∀ n : ℤ, Countable (G ⟶ X⟦n⟧)

end

end ObjectProperty

namespace IsCompactObject

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D]
  [HasCountableCoproducts D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]

/-- Lemma 22.38.3 (0CRM), compact-generator form: suppose `G` is a compact weak generator and
all shifted endomorphism types `G ⟶ G⟦n⟧` are countable. An object `X` has countable
shifted Hom types `G ⟶ X⟦n⟧` if and only if it is a sequential homotopy colimit of compact
objects.

For the derived category of a differential graded algebra, take `G` to be the regular module;
then these shifted represented Hom types compute the cohomology of the algebra and of `X`. -/
@[stacks 0CRM "countable compact-generator criterion"]
theorem sequentialHomotopyColimits_iff_countableShiftedHom
    (G X : D) (hG_compact : IsCompactObject G) (hG_generator : IsWeakGenerator G)
    (hG_countable : countableShiftedHomFrom G G) :
    sequentialHomotopyColimits (IsCompactObject : ObjectProperty D) X ↔
      countableShiftedHomFrom G X := sorry

end IsCompactObject

end CategoryTheory
