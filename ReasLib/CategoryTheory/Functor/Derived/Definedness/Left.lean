/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.Definedness.Domain
public import ReasLib.CategoryTheory.Localization.Lifting.Computation
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Equivalence.Invariance
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Left-Derived Functors on Their Domain of Definition

This leaf packages raw pointwise left-derived values into a functor on the full subcategory where
they are defined.  Its construction is dual to `Definedness.Right` and remains independent of a
global pointwise derived functor.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Localization MorphismProperty ObjectProperty

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D)

namespace Functor.LeftDerived.Definedness

/-- a denominator between objects where the pointwise left-derived value is
defined induces an isomorphism of raw left-derived values. -/
@[stacks 05SE]
theorem valueMap.isIso_of_mem {X Y : D} (f : X ⟶ Y) (hf : S f)
    [F.HasPointwiseLeftDerivedFunctorAt S X] [F.HasPointwiseLeftDerivedFunctorAt S Y] :
    IsIso (CategoryTheory.Functor.LeftDerived.Value.map F S f) := sorry

/-- the pointwise left-derived value of `F`, assembled into a functor on its full
domain of definition. -/
@[stacks 05SE]
noncomputable def functor : Domain F S ⥤ D' where
  obj X := CategoryTheory.Functor.LeftDerived.Value.obj F S X.obj
  map f := CategoryTheory.Functor.LeftDerived.Value.map F S f.hom
  map_id X := CategoryTheory.Functor.LeftDerived.Value.map_id F S X.obj
  map_comp f g := CategoryTheory.Functor.LeftDerived.Value.map_comp F S f.hom g.hom

/-- The restricted left-derived functor evaluates to the raw pointwise left-derived value. -/
@[simp, stacks 05SE]
theorem functor.obj (X : Domain F S) :
    (functor F S).obj X = CategoryTheory.Functor.LeftDerived.Value.obj F S X.obj := sorry

/-- The restricted left-derived functor maps a morphism by the raw pointwise value map. -/
@[simp, stacks 05SE]
theorem functor.map {X Y : Domain F S} (f : X ⟶ Y) :
    (functor F S).map f = CategoryTheory.Functor.LeftDerived.Value.map F S f.hom := sorry

/-- the restricted left-derived functor inverts the restricted localization
class. -/
@[stacks 05SE]
theorem functor.isInvertedBy :
    (system F S).IsInvertedBy (functor F S) :=
  sorry

/-- the canonical factorization of the restricted left-derived functor through the
localization of its domain of definition. -/
@[stacks 05SE]
noncomputable abbrev localizationFactorization :
    (system F S).Localization ⥤ D' :=
  Localization.lift (functor F S)
    (functor.isInvertedBy F S)
    (system F S).Q

/-- The canonical factorization isomorphism from the localized left-derived functor back to the
raw pointwise left-derived functor on its domain of definition. -/
@[stacks 05SE]
noncomputable def facIso :
    (system F S).Q ⋙ localizationFactorization F S ≅ functor F S :=
  Localization.Lifting.iso (system F S).Q (system F S) (functor F S)
    (localizationFactorization F S)

namespace facIso

/-- Naturality of the forward comparison for the localized left-derived factorization,
expressed using the raw pointwise value map. -/
@[reassoc (attr := simp), stacks 05SE "left-derived factorization comparison naturality"]
theorem hom_naturality {X Y : Domain F S} (f : X ⟶ Y) :
    (localizationFactorization F S).map ((system F S).Q.map f) ≫
        (facIso F S).hom.app Y =
      (facIso F S).hom.app X ≫ CategoryTheory.Functor.LeftDerived.Value.map F S f.hom := sorry

/-- Naturality of the inverse comparison for the localized left-derived factorization,
expressed using the raw pointwise value map. -/
@[reassoc (attr := simp), stacks 05SE "inverse left-derived factorization naturality"]
theorem inv_naturality {X Y : Domain F S} (f : X ⟶ Y) :
    CategoryTheory.Functor.LeftDerived.Value.map F S f.hom ≫ (facIso F S).inv.app Y =
      (facIso F S).inv.app X ≫
        (localizationFactorization F S).map ((system F S).Q.map f) := sorry

end facIso

namespace localizationFactorization

/-- The localized left-derived functor maps a morphism coming from its localization functor by
conjugating the raw pointwise value map with the canonical factorization comparison. -/
@[simp, reassoc (attr := simp), stacks 05SE]
theorem map_Q {X Y : Domain F S} (f : X ⟶ Y) :
    (localizationFactorization F S).map ((system F S).Q.map f) =
      (facIso F S).hom.app X ≫ CategoryTheory.Functor.LeftDerived.Value.map F S f.hom ≫
        (facIso F S).inv.app Y := sorry

end localizationFactorization

end Functor.LeftDerived.Definedness



end CategoryTheory
