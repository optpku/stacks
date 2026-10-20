/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Base-indexed properties on slice categories

This file records object and morphism properties that vary with the base of a
slice category.  The definitions are category-theoretic; schemes are only one
downstream specialization.
-/

@[expose] public section

open CategoryTheory.Limits

universe u v

namespace CategoryTheory.Over

variable {C : Type u} [Category.{v} C]

/-- A family of object properties on slice categories, indexed by the base object. -/
@[stacks 01JZ "base-indexed slice-object properties"]
abbrev ObjectPropertyFamily (C : Type u) [Category.{v} C] :=
  (S : C) → ObjectProperty (Over S)

/-- A family of morphism properties on slice categories, indexed by the base object. -/
@[stacks 01JZ "base-indexed slice-morphism properties"]
abbrev MorphismPropertyFamily (C : Type u) [Category.{v} C] :=
  (S : C) → MorphismProperty (Over S)

/-- Definition 26.18.3 (1): a base-indexed family of object properties is stable under base
change when pullback along every map of bases preserves the property. -/
@[stacks 01JZ]
class ObjectPropertyFamily.IsStableUnderBaseChange
    (P : ObjectPropertyFamily C) : Prop where
  /-- A pullback of an object over a varying base retains the indexed property. -/
  of_isPullback ⦃S S' : C⦄ ⦃g : S' ⟶ S⦄ ⦃X : Over S⦄ ⦃X' : Over S'⦄
      ⦃i : X'.left ⟶ X.left⦄ (sq : IsPullback i X'.hom X.hom g) :
    P S X → P S' X'

/-- Definition 26.18.3 (2): a base-indexed family of slice-morphism properties is stable under
base change when maps induced between pullback objects preserve the property. -/
@[stacks 01JZ]
class MorphismPropertyFamily.IsStableUnderBaseChange
    (P : MorphismPropertyFamily C) : Prop where
  /-- A morphism induced between two pullback objects retains the indexed property. -/
  of_isPullback ⦃S S' : C⦄ ⦃g : S' ⟶ S⦄ ⦃X Y : Over S⦄ ⦃X' Y' : Over S'⦄
      ⦃f : X ⟶ Y⦄ ⦃f' : X' ⟶ Y'⦄ ⦃i : X'.left ⟶ X.left⦄
      ⦃j : Y'.left ⟶ Y.left⦄ (target : IsPullback j Y'.hom Y.hom g)
      (source : IsPullback i f'.left f.left j) :
    P S f → P S' f'

/-- A stable base-indexed object property is preserved by mathlib's chosen pullback functor. -/
@[stacks 01JZ "pullback of a stable slice-object property"]
theorem ObjectPropertyFamily.IsStableUnderBaseChange.pullback
    {P : ObjectPropertyFamily C} [P.IsStableUnderBaseChange]
    {S S' : C} (g : S' ⟶ S) [HasPullbacksAlong g] {X : Over S} (hX : P S X) :
    P S' ((Over.pullback g).obj X) := sorry

/-- A stable base-indexed morphism property is preserved on maps by mathlib's chosen pullback
functor. -/
@[stacks 01JZ "pullback of a stable slice-morphism property"]
theorem MorphismPropertyFamily.IsStableUnderBaseChange.pullbackMap
    {P : MorphismPropertyFamily C} [P.IsStableUnderBaseChange]
    {S S' : C} (g : S' ⟶ S) [HasPullbacksAlong g]
    {X Y : Over S} (f : X ⟶ Y) (hf : P S f) :
    P S' ((Over.pullback g).map f) := sorry

end CategoryTheory.Over

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C]

/-- The base-indexed family of slice-object properties induced by a morphism property. -/
@[stacks 01JZ "slice-object family induced by a morphism property"]
abbrev overObjFamily (P : MorphismProperty C) : Over.ObjectPropertyFamily C :=
  fun _ ↦ P.overObj

/-- The base-indexed family of slice-morphism properties induced by a morphism property. -/
@[stacks 01JZ "slice-morphism family induced by a morphism property"]
abbrev overFamily (P : MorphismProperty C) : Over.MorphismPropertyFamily C :=
  fun _ ↦ P.over

/-- Stability of a morphism property under base change is inherited by its induced
slice-object family. -/
@[stacks 01JZ "slice-object family stability instance", instance]
instance IsStableUnderBaseChange.overObjFamily
    (P : MorphismProperty C) [P.IsStableUnderBaseChange] :
    P.overObjFamily.IsStableUnderBaseChange := sorry

/-- Stability of a morphism property under base change is inherited by its induced
slice-morphism family. -/
@[stacks 01JZ "slice-morphism family stability instance", instance]
instance IsStableUnderBaseChange.overFamily
    (P : MorphismProperty C) [P.IsStableUnderBaseChange] :
    P.overFamily.IsStableUnderBaseChange := sorry

/-- A morphism property is stable under base change exactly when its induced slice-object
family is stable under base change. -/
@[stacks 01JZ "base-change stability via slice objects"]
theorem isStableUnderBaseChange_iff_overObjFamily (P : MorphismProperty C) :
    P.IsStableUnderBaseChange ↔ P.overObjFamily.IsStableUnderBaseChange := sorry

/-- A morphism property is stable under base change exactly when its induced slice-morphism
family is stable under base change. -/
@[stacks 01JZ "base-change stability via slice morphisms"]
theorem isStableUnderBaseChange_iff_overFamily (P : MorphismProperty C) :
    P.IsStableUnderBaseChange ↔ P.overFamily.IsStableUnderBaseChange := sorry

variable {P : MorphismProperty C} [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
variable {S : C} [HasBinaryProducts (Over S)]
variable {A B D E : Over S}

/-- A binary product map in a slice satisfies a property stable under base change and
composition whenever its two component maps do. -/
@[stacks 01KU "product maps in a slice"]
theorem overProdMap (f : A ⟶ B) (g : D ⟶ E) (hf : P f.left) (hg : P g.left) :
    P (Limits.prod.map f g).left := sorry

end CategoryTheory.MorphismProperty
