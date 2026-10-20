/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Selected objects over a target

This leaf owns the canonical diagram and cocone obtained by selecting objects
of an over category and forgetting their maps to a fixed target.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CategoryTheory.ObjectProperty.Over

variable {C : Type u} [Category.{v} C] {X : C}

/-- The diagram in `C` formed by the sources of objects selected by `P` over
the fixed target `X`. -/
@[stacks 07C3 "selected over-object diagram"]
abbrev forgetDiagram (P : ObjectProperty (CategoryTheory.Over X)) :
    P.FullSubcategory ⥤ C :=
  P.ι ⋙ CategoryTheory.Over.forget X

/-- The canonical cocone from the sources of the `P`-objects over `X` to
`X`. -/
@[stacks 07C3 "selected over-object cocone"]
abbrev forgetCocone (P : ObjectProperty (CategoryTheory.Over X)) :
    Cocone (forgetDiagram P) :=
  (CategoryTheory.Over.forgetCocone X).whisker P.ι

/-- A leg of the selected over-object cocone is the structure morphism of the
corresponding over-object. -/
@[simp, stacks 07C3 "selected over-object cocone leg"]
theorem forgetCocone_ι_app
    (P : ObjectProperty (CategoryTheory.Over X)) (A : P.FullSubcategory) :
    (forgetCocone P).ι.app A = A.obj.hom := sorry

/-- Restricting the selected cocone for a larger object property along an
inclusion of object properties gives the selected cocone for the smaller one. -/
@[simp, stacks 07C3 "selected over-object cocone restriction"]
theorem forgetCocone_whisker_ιOfLE
    {P Q : ObjectProperty (CategoryTheory.Over X)} (hPQ : P ≤ Q) :
    (forgetCocone Q).whisker (ObjectProperty.ιOfLE hPQ) = forgetCocone P := sorry

end CategoryTheory.ObjectProperty.Over
