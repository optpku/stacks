/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Reflectors of Full Subcategories

@stack 0G3E

This file owns the data of a reflector onto a full subcategory defined by an object property.
It also provides the noncanonical construction from an explicit right-adjoint witness.  Consumers
can pass the reflector data explicitly without installing a global `Reflective` instance.
-/

@[expose] public section

noncomputable section

namespace CategoryTheory.ObjectProperty

universe v u

variable {C : Type u} [Category.{v} C]

/-- A chosen reflector onto the full subcategory determined by `P`. -/
@[stacks 0G3E "reflector of an object-property subcategory"]
structure Reflector (P : ObjectProperty C) where
  /-- The functor sending an ambient object to its reflected object. -/
  toFullSubcategory : C ⥤ P.FullSubcategory
  /-- The universal reflection adjunction. -/
  adjunction : toFullSubcategory ⊣ P.ι

namespace Reflector

/-- The ambient endofunctor induced by a reflector. -/
@[stacks 0G3E "reflection endofunctor"]
def reflection {P : ObjectProperty C} (R : Reflector P) : C ⥤ C :=
  R.toFullSubcategory ⋙ P.ι

/-- The universal map from an object to its reflection. -/
@[stacks 0G3E "unit of an object-property reflection"]
def unit {P : ObjectProperty C} (R : Reflector P) : 𝟭 C ⟶ R.reflection :=
  R.adjunction.unit

/-- A noncanonical reflector built from an explicit right-adjoint witness for the inclusion. -/
@[stacks 0G3E "reflector from a right adjoint"]
noncomputable def ofIsRightAdjoint (P : ObjectProperty C) (h : P.ι.IsRightAdjoint) :
    Reflector P := by
  -- Local instance justification (noncanonical choice): the explicit witness `h` selects the adjoint only inside this constructor and must not become a global instance.
  letI : P.ι.IsRightAdjoint := h
  exact ⟨P.ι.leftAdjoint, Adjunction.ofIsRightAdjoint P.ι⟩

end Reflector

end CategoryTheory.ObjectProperty
