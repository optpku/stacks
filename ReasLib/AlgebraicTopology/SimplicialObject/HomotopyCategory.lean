/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Homotopy.Relation
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 08RJ

# Homotopy category of simplicial objects

The zigzag simplicial homotopy relation is compatible with composition, hence defines a
quotient category of simplicial objects. This file provides that quotient and its canonical
functor, together with the characteristic equality API for morphisms. Fullness and essential
surjectivity are inherited directly from Mathlib's general quotient-functor instances.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.SimplicialObject

/-- Remark 14.26.5 (08RJ): the homotopy category of simplicial objects in `C`, obtained by
identifying homotopic morphisms. -/
@[stacks 08RJ "simplicial homotopy category"]
def HomotopyCategory (C : Type u) [Category.{v} C] :=
  CategoryTheory.Quotient (homotopyRel C)

/-- The category structure on the simplicial homotopy category inherited from the quotient. -/
@[stacks 08RJ "category structure on the simplicial homotopy category"]
instance (C : Type u) [Category.{v} C] : Category (HomotopyCategory C) :=
  inferInstanceAs (Category (CategoryTheory.Quotient (homotopyRel C)))

namespace HomotopyCategory

/-- The canonical functor from simplicial objects to their homotopy category. -/
@[stacks 08RJ "canonical functor to the simplicial homotopy category"]
def quotient (C : Type u) [Category.{v} C] :
    SimplicialObject C ⥤ HomotopyCategory C :=
  CategoryTheory.Quotient.functor (homotopyRel C)

/-- Two morphisms have equal images in the homotopy category exactly when they are homotopic. -/
@[stacks 08RJ "equality in the simplicial homotopy category"]
theorem quotient.map_eq_iff {C : Type u} [Category.{v} C]
    {X Y : SimplicialObject C} (f g : X ⟶ Y) :
    (quotient C).map f = (quotient C).map g ↔ Homotopic f g := sorry

/-- Homotopic morphisms have equal images under the canonical quotient functor. -/
@[stacks 08RJ "homotopic maps agree in the simplicial homotopy category"]
theorem quotient.map_eq_of_homotopic {C : Type u} [Category.{v} C]
    {X Y : SimplicialObject C} (f g : X ⟶ Y) (h : Homotopic f g) :
    (quotient C).map f = (quotient C).map g := sorry

end HomotopyCategory

end CategoryTheory.SimplicialObject
