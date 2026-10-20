/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

/-!
# Algebraic spaces flat over a base

The full subcategory of algebraic spaces whose structure morphism to a fixed
base is flat.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

/-- The object property on `Over Y` consisting of flat structure morphisms. -/
abbrev flatOverProperty {S : Scheme.{u}} (Y : AlgebraicSpace S) :
    ObjectProperty (Over Y) :=
  MorphismProperty.overObj (@Flat S)

/-- An object over `Y` satisfies `flatOverProperty Y` exactly when its structure
morphism is flat. -/
theorem flatOverProperty_iff {S : Scheme.{u}} (Y : AlgebraicSpace S) (Z : Over Y) :
    flatOverProperty Y Z ↔ Flat Z.hom :=
  sorry

/-- The full subcategory of algebraic spaces whose structure morphism to `Y` is
flat. -/
abbrev FlatOver {S : Scheme.{u}} (Y : AlgebraicSpace S) : Type (u + 1) :=
  (flatOverProperty Y).FullSubcategory

namespace FlatOver

/-- The inclusion of algebraic spaces flat over `Y` into all algebraic spaces
over `Y`. -/
abbrev inclusion {S : Scheme.{u}} (Y : AlgebraicSpace S) : FlatOver Y ⥤ Over Y :=
  (flatOverProperty Y).ι

/-- The inclusion of a flat algebraic space over `Y` remembers its underlying
object of `Over Y`. -/
theorem inclusion_obj {S : Scheme.{u}} {Y : AlgebraicSpace S} (Z : FlatOver Y) :
    (inclusion Y).obj Z = Z.obj :=
  sorry

/-- The structure morphism of an object of `FlatOver Y` is flat. -/
instance instFlatHom {S : Scheme.{u}} {Y : AlgebraicSpace S} (Z : FlatOver Y) :
    Flat Z.obj.hom :=
  Z.property

end FlatOver

end AlgebraicGeometry.AlgebraicSpace
