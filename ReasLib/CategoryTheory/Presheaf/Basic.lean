/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Opposites

/-!
# Type-valued presheaves

This module gives the project-wide owner name for a contravariant `Type`-valued functor.
Mathlib represents this directly as a functor category; the abbreviation keeps that canonical
representation while making a reusable presheaf API discoverable.
-/

@[expose] public section

universe u v w

namespace CategoryTheory

/-- A `Type`-valued presheaf on `C`, definitionally the functor category `Cᵒᵖ ⥤ Type w`. -/
abbrev Presheaf (C : Type u) [Category.{v} C] := Cᵒᵖ ⥤ Type w

end CategoryTheory
