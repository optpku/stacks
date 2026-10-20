/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommAlgCat.LocalProperty

/-!
# The category of local algebras

This module defines the category of local algebras over a fixed commutative ring.
-/

@[expose] public section

open CategoryTheory

universe v₁ u₁ u v

/-- The category of local `A`-algebras whose structure maps and morphisms are local. -/
def LocalAlgCat (A : Type u₁) [CommRing A] :=
  WideSubcategory (LocalAlgCat.morphismProperty.{u₁, v₁} A)

variable (A : Type u) [CommRing A]

/-- The category structure on local algebras inherited from the ambient wide subcategory. -/
instance LocalAlgCat.category : Category (LocalAlgCat.{v} A) :=
  inferInstanceAs (Category (WideSubcategory (LocalAlgCat.morphismProperty.{u, v} A)))
