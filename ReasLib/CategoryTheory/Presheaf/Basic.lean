/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites

/-!
# Type-valued presheaves

This module gives the project-wide owner name for a contravariant `Type`-valued functor.
Mathlib represents this directly as a functor category; the abbreviation keeps that canonical
representation while making a reusable presheaf API discoverable.
-/

@[expose] public section

universe u v w uC vC uA vA

namespace CategoryTheory

/-- A `Type`-valued presheaf on `C`, definitionally the functor category `Cᵒᵖ ⥤ Type w`. -/
abbrev Presheaf (C : Type u) [Category.{v} C] := Cᵒᵖ ⥤ Type w

/-- An `A`-valued presheaf on `C`, definitionally a functor `Cᵒᵖ ⥤ A`. -/
abbrev PresheafWithValues (C : Type uC) [Category.{vC} C] (A : Type uA)
    [Category.{vA} A] := Cᵒᵖ ⥤ A

namespace PresheafWithValues

/-- A morphism between `A`-valued presheaves, definitionally a natural transformation. -/
abbrev Hom {C : Type uC} [Category.{vC} C] {A : Type uA} [Category.{vA} A]
    (F G : PresheafWithValues C A) := NatTrans F G

end PresheafWithValues

end CategoryTheory
