/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Epi
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

/-!
# Flat morphisms and schemes over a base

This file defines schemes flat over a fixed base and their base-change functor,
and proves faithfulness of base change along surjective flat morphisms.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

noncomputable section

namespace AlgebraicGeometry.Flat

/-- Base change along a surjective flat morphism of schemes is faithful. -/
theorem instFaithfulOverPullbackOfSurjective {S' S : Scheme.{u}} (h : S' ⟶ S)
    [Flat h] [Surjective h] : (Over.pullback h).Faithful := sorry

end AlgebraicGeometry.Flat

namespace AlgebraicGeometry

/-- The object property on `Over S` consisting of flat structure morphisms. -/
abbrev flatOverProperty (S : Scheme.{u}) : ObjectProperty (Over S) :=
  MorphismProperty.overObj @Flat

/-- An object over `S` satisfies `flatOverProperty S` exactly when its structure morphism is
flat. -/
theorem flatOverProperty_iff (S : Scheme.{u}) (Z : Over S) :
    flatOverProperty S Z ↔ Flat Z.hom := sorry

/-- The full subcategory of schemes whose structure morphism to `S` is flat. -/
abbrev FlatOver (S : Scheme.{u}) : Type (u + 1) :=
  (flatOverProperty S).FullSubcategory

namespace FlatOver

/-- The inclusion of schemes flat over `S` into all schemes over `S`. -/
abbrev inclusion (S : Scheme.{u}) : FlatOver S ⥤ Over S :=
  (flatOverProperty S).ι

/-- The inclusion of a flat scheme over `S` remembers its underlying object of `Over S`. -/
theorem inclusion_obj (S : Scheme.{u}) (Z : FlatOver S) :
    (inclusion S).obj Z = Z.obj := sorry

/-- The structure morphism of an object of `FlatOver S` is flat. -/
theorem instFlatHom {S : Scheme.{u}} (Z : FlatOver S) : Flat Z.obj.hom :=
  Z.property

/-- Base change preserves the property of having a flat structure morphism. -/
theorem baseChange_mem {S S' : Scheme.{u}} (g : S' ⟶ S) (Z : Over S)
    (hZ : flatOverProperty S Z) :
    flatOverProperty S' ((Over.pullback g).obj Z) := sorry

/-- The base-change functor between categories of flat schemes over a base. -/
def baseChange {S S' : Scheme.{u}} (g : S' ⟶ S) : FlatOver S ⥤ FlatOver S' :=
  ObjectProperty.FullSubcategory.restrict (Over.pullback g) (baseChange_mem g)

/-- The underlying object of flat base change is the ordinary base change in `Over`. -/
theorem baseChange_obj {S S' : Scheme.{u}} (g : S' ⟶ S) (Z : FlatOver S) :
    ((baseChange g).obj Z).obj = (Over.pullback g).obj Z.obj := sorry

end FlatOver

end AlgebraicGeometry
