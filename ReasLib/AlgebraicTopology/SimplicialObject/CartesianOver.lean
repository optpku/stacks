/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered
public import ReasLib.AlgebraicTopology.SimplicialObject.Cartesian

/-!
# Cartesian simplicial objects over a fixed base

The full subcategory of `Over X` spanned by cartesian structure morphisms.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- The category of simplicial objects equipped with a cartesian morphism to `X`. -/
abbrev CartesianOver (X : SimplicialObject C) :=
  ObjectProperty.FullSubcategory fun (Y : Over X) ↦ IsCartesian Y.hom

namespace CartesianOver

variable {X : SimplicialObject C}

/-- Construct an object cartesian over `X` from a cartesian structure morphism. -/
def ofHom {Y : SimplicialObject C} (a : Y ⟶ X) (ha : IsCartesian a) : CartesianOver X :=
  ⟨Over.mk a, ha⟩

/-- The structure morphism of an object cartesian over `X` is cartesian. -/
theorem isCartesian (Y : CartesianOver X) : IsCartesian Y.obj.hom := sorry

/-- The underlying object of `ofHom a ha` is `Over.mk a`. -/
theorem ofHom_obj {Y : SimplicialObject C} (a : Y ⟶ X) (ha : IsCartesian a) :
    (ofHom a ha).obj = Over.mk a := sorry

end CartesianOver

/-- A morphism of simplicial objects is cartesian iff it is equifibered. -/
theorem isCartesian_iff_equifibered {Y X : SimplicialObject C} (a : Y ⟶ X) :
    IsCartesian a ↔ NatTrans.Equifibered a := sorry

end CategoryTheory.SimplicialObject
