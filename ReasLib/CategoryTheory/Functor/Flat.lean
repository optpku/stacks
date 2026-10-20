/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Representably flat full-subcategory inclusions

For a full-subcategory inclusion, the defining comma categories for representable flatness are
exactly the categories of arrows from an ambient object to an object of the subcategory.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]

/-- A full-subcategory inclusion is representably flat when every category of arrows from an
ambient object to the subcategory is cofiltered. -/
@[stacks 0GZE "cofiltered full-subcategory inclusion", instance]
theorem representablyFlat_ι (P : ObjectProperty C)
    [∀ U : C, IsCofiltered (StructuredArrow U P.ι)] : RepresentablyFlat P.ι := sorry

end CategoryTheory.ObjectProperty
