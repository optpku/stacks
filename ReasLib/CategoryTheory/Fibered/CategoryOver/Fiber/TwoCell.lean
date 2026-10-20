/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber.Cartesian
public import ReasLib.CategoryTheory.Fibered.Criteria
import Mathlib.Tactic.CrossRefAttribute

/-!
# Two-cells and the base projection of a fibred category

This leaf owns the underlying transformation views, their constructor, and the canonical
morphism from a fibred category to its base.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v

namespace CategoryTheory

open BasedFunctor
open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver

variable {X Y : FiberedCategoryOver C}

/-- The underlying based natural transformation of a `2`-morphism between morphisms of
fibred categories. -/
abbrev toBasedNatTrans {F G : X ⟶ Y} (eta : F ⟶ G) :
    toBasedFunctor F ⟶ toBasedFunctor G :=
  eta.hom

/-- The ordinary natural transformation on total categories underlying a `2`-morphism of
fibred-category morphisms. -/
abbrev toNatTrans {F G : X ⟶ Y} (eta : F ⟶ G) :
    toFunctor F ⟶ toFunctor G :=
  (toBasedNatTrans eta).toNatTrans

/-- Build a `2`-morphism of fibred-category morphisms from a based natural transformation. -/
def ofBasedNatTrans {F G : X ⟶ Y}
    (eta : toBasedFunctor F ⟶ toBasedFunctor G) : F ⟶ G :=
  ObjectProperty.homMk eta

/-- Projecting a `2`-morphism built by `ofBasedNatTrans` recovers the supplied based natural
transformation. -/
@[simp]
theorem ofBasedNatTrans.toBasedNatTrans {F G : X ⟶ Y}
    (eta : toBasedFunctor F ⟶ toBasedFunctor G) :
    toBasedNatTrans (ofBasedNatTrans eta) = eta := sorry

/-- The projection of a fibred category to its base preserves strongly cartesian morphisms. -/
theorem toBase.preservesStronglyCartesian
    (X : FiberedCategoryOver.{u, v, u, v} C) :
    PreservesStronglyCartesian X.toBasedCategory.toBase := sorry
/- Proof strategy: the image of any source arrow is its base arrow. Apply
`Functor.IsStronglyCartesian.id` to that arrow and transport along the definition of
`BasedCategory.toBase`. -/

/-- The canonical morphism from a fibred category to the base equipped with its identity
fibration. -/
def toBase (X : FiberedCategoryOver.{u, v, u, v} C) :
    X ⟶ ofFunctor (𝟭 C) :=
  ofBasedFunctor X.toBasedCategory.toBase (toBase.preservesStronglyCartesian X)

/-- Any `2`-morphism between morphisms of fibred categories is vertical over the identity on
each source object. -/
theorem TwoCell.app.isHomLiftId
    {X Y : FiberedCategoryOver C} {F G : X ⟶ Y}
    (τ : F ⟶ G) (a : X.total) :
    Functor.IsHomLift Y.p (𝟙 (X.p.obj a)) (τ.hom.toNatTrans.app a) := sorry
/- Proof strategy: use the verticality witness carried by the underlying `BasedNatTrans`, namely
`τ.hom.isHomLift rfl`. -/

end FiberedCategoryOver

end CategoryTheory
