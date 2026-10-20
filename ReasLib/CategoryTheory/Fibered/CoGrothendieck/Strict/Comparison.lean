/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Strict.SplitCleavage
public import ReasLib.CategoryTheory.Fibered.Split.Transport
import Mathlib.Tactic.CrossRefAttribute

/-!
# Strict co-Grothendieck comparison

This leaf constructs the strict comparison from explicit `SplitCleavage` data, its inverse, and
the stable object/map computation API in the total category and over the base.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace Functor.SplitCleavage

variable {p : S ⥤ C}

section ComparisonImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The forward comparison sends an object to itself in the standard fiber over its image. -/
private def forward.obj (χ : p.SplitCleavage) (x : S) :
    Pseudofunctor.CoGrothendieck χ.toCatPresheaf.toPseudofunctor' :=
  { base := p.obj x
    fiber := ⟨x, rfl⟩ }

/-- The forward comparison factors an ambient morphism through the selected cartesian lift of its
base image. -/
private noncomputable def forward.map (χ : p.SplitCleavage)
    {x y : S} (f : x ⟶ y) :
    forward.obj χ x ⟶ forward.obj χ y :=
  { base := p.map f
    fiber := χ.toCleavage.verticalFactor f }

/-- The forward comparison preserves identity morphisms. -/
private theorem forward.mapId (χ : p.SplitCleavage) (x : S) :
    forward.map χ (𝟙 x) = 𝟙 (forward.obj χ x) := sorry

/-- The forward comparison preserves composition of ambient morphisms. -/
private theorem forward.mapComp (χ : p.SplitCleavage)
    {x y z : S} (f : x ⟶ y) (g : y ⟶ z) :
    forward.map χ (f ≫ g) =
      forward.map χ f ≫ forward.map χ g := sorry

/-- The raw forward functor from the original total category to its strict co-Grothendieck model.
Its object and morphism payload are explicit; only the functor laws are deferred. -/
private noncomputable def forward.functor (χ : p.SplitCleavage) :
    S ⥤ Pseudofunctor.CoGrothendieck χ.toCatPresheaf.toPseudofunctor' where
  obj := forward.obj χ
  map := forward.map χ
  map_id := forward.mapId χ
  map_comp := forward.mapComp χ

/-- The raw forward comparison commutes strictly with the projections to the base. -/
private theorem forward.comm (χ : p.SplitCleavage) :
    forward.functor χ ⋙
        Pseudofunctor.CoGrothendieck.forget χ.toCatPresheaf.toPseudofunctor' = p := sorry

/-- The inverse comparison forgets the standard-fiber witness of a co-Grothendieck object. -/
private def inverse.obj (χ : p.SplitCleavage)
    (X : Pseudofunctor.CoGrothendieck χ.toCatPresheaf.toPseudofunctor') : S :=
  X.fiber.1

/-- The inverse comparison composes the fiber component with the selected cartesian arrow over
the base component. -/
private noncomputable def inverse.map (χ : p.SplitCleavage)
    {X Y : Pseudofunctor.CoGrothendieck χ.toCatPresheaf.toPseudofunctor'} (f : X ⟶ Y) :
    inverse.obj χ X ⟶ inverse.obj χ Y :=
  f.fiber.1 ≫ χ.toCleavage.cartesianHom f.base Y.fiber

/-- The inverse comparison preserves identity co-Grothendieck morphisms. -/
private theorem inverse.mapId (χ : p.SplitCleavage)
    (X : Pseudofunctor.CoGrothendieck χ.toCatPresheaf.toPseudofunctor') :
    inverse.map χ (𝟙 X) = 𝟙 (inverse.obj χ X) := sorry

/-- The inverse comparison preserves composition of co-Grothendieck morphisms. -/
private theorem inverse.mapComp (χ : p.SplitCleavage)
    {X Y Z : Pseudofunctor.CoGrothendieck χ.toCatPresheaf.toPseudofunctor'}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    inverse.map χ (f ≫ g) =
      inverse.map χ f ≫ inverse.map χ g := sorry

/-- The raw inverse functor from the strict co-Grothendieck model to the original total category.
Its data forget the fiber witness and compose with the selected cartesian lift. -/
private noncomputable def inverse.functor (χ : p.SplitCleavage) :
    Pseudofunctor.CoGrothendieck χ.toCatPresheaf.toPseudofunctor' ⥤ S where
  obj := inverse.obj χ
  map := inverse.map χ
  map_id := inverse.mapId χ
  map_comp := inverse.mapComp χ

/-- The forward and inverse comparison functors compose to the identity on the original total
category. -/
private theorem unit (χ : p.SplitCleavage) :
    𝟭 S = forward.functor χ ⋙ inverse.functor χ := sorry

/-- The inverse and forward comparison functors compose to the identity on the co-Grothendieck
model. -/
private theorem counit (χ : p.SplitCleavage) :
    inverse.functor χ ⋙ forward.functor χ =
      𝟭 (Pseudofunctor.CoGrothendieck χ.toCatPresheaf.toPseudofunctor') := sorry

end Implementation

/-- The canonical comparison over `C` from an explicitly split fibred category to the
co-Grothendieck model of its strict fiber presheaf. -/
@[stacks 02XW "forward strict co-Grothendieck comparison"]
noncomputable def CoGrothendieck.functor (χ : p.SplitCleavage) :
    BasedCategory.ofFunctor p ⥤ᵇ
      BasedCategory.ofFunctor
        (Pseudofunctor.CoGrothendieck.forget χ.toCatPresheaf.toPseudofunctor') where
  toFunctor := Implementation.forward.functor χ
  w := Implementation.forward.comm χ

/-- The strict co-Grothendieck comparison commutes with the two projections to `C`. -/
@[simp, stacks 02XW "projection formula for the strict co-Grothendieck comparison"]
theorem CoGrothendieck.functor.comm (χ : p.SplitCleavage) :
    (CoGrothendieck.functor χ).toFunctor ⋙
        Pseudofunctor.CoGrothendieck.forget χ.toCatPresheaf.toPseudofunctor' = p := sorry

/-- The object map of the strict co-Grothendieck comparison retains the original base object. -/
@[simp, stacks 02XW "object-base formula for the strict co-Grothendieck comparison"]
theorem CoGrothendieck.functor.obj.base (χ : p.SplitCleavage) (x : S) :
    ((CoGrothendieck.functor χ).toFunctor.obj x).base = p.obj x := sorry

/-- The fiber object is the original object equipped with its reflexive projection equality. -/
@[simp, stacks 02XW "object-fiber formula for the strict co-Grothendieck comparison"]
theorem CoGrothendieck.functor.obj.fiber (χ : p.SplitCleavage) (x : S) :
    ((CoGrothendieck.functor χ).toFunctor.obj x).fiber =
      (Functor.Fiber.mk (p := p) (a := x) rfl : p.Fiber (p.obj x)) := sorry

/-- Forgetting the displayed-fiber witness recovers the original total-category object. -/
@[simp]
theorem CoGrothendieck.functor.obj.fiber.val (χ : p.SplitCleavage) (x : S) :
    ((CoGrothendieck.functor χ).toFunctor.obj x).fiber.1 = x := sorry

/-- The morphism map of the comparison retains the original base map. -/
@[simp, stacks 02XW "map-base formula for the strict co-Grothendieck comparison"]
theorem CoGrothendieck.functor.map.base (χ : p.SplitCleavage)
    {x y : S} (f : x ⟶ y) :
    ((CoGrothendieck.functor χ).toFunctor.map f).base = p.map f := sorry

/-- The fiber component is the canonical vertical factor through the selected cartesian arrow. -/
@[simp, stacks 02XW "map-fiber formula for the strict co-Grothendieck comparison"]
theorem CoGrothendieck.functor.map.fiber (χ : p.SplitCleavage)
    {x y : S} (f : x ⟶ y) :
    ((CoGrothendieck.functor χ).toFunctor.map f).fiber =
      χ.toCleavage.verticalFactor f := sorry

/-- The underlying total-category arrow of the fiber component is the ambient vertical factor. -/
@[simp]
theorem CoGrothendieck.functor.map.fiber.val (χ : p.SplitCleavage)
    {x y : S} (f : x ⟶ y) :
    ((CoGrothendieck.functor χ).toFunctor.map f).fiber.1 =
      χ.toCleavage.verticalFactorHom f := sorry

/-- The fiber component lies over the identity of the source base object. -/
instance CoGrothendieck.functor.map.fiber.isHomLift (χ : p.SplitCleavage)
    {x y : S} (f : x ⟶ y) :
    p.IsHomLift (𝟙 (p.obj x))
      ((CoGrothendieck.functor χ).toFunctor.map f).fiber.1 := sorry

/-- The fiber component followed by the selected cartesian arrow is the original morphism. -/
@[simp]
theorem CoGrothendieck.functor.map.fiber.fac (χ : p.SplitCleavage)
    {x y : S} (f : x ⟶ y) :
    ((CoGrothendieck.functor χ).toFunctor.map f).fiber.1 ≫
        χ.toCleavage.cartesianHom (p.map f)
          (Functor.Fiber.mk (p := p) (a := y) rfl : p.Fiber (p.obj y)) =
      f := sorry

/-- The inverse total functor from the strict co-Grothendieck model back to the original total
category. It forgets the displayed fiber witness on objects and composes the fiber component with
the selected cartesian arrow on morphisms. -/
noncomputable def CoGrothendieck.inverse (χ : p.SplitCleavage) :
    Pseudofunctor.CoGrothendieck χ.toCatPresheaf.toPseudofunctor' ⥤ S :=
  Implementation.inverse.functor χ

/-- The inverse total functor forgets the displayed fiber witness of an object. -/
@[simp]
theorem CoGrothendieck.inverse.obj (χ : p.SplitCleavage)
    (X : Pseudofunctor.CoGrothendieck χ.toCatPresheaf.toPseudofunctor') :
    (CoGrothendieck.inverse χ).obj X = X.fiber.1 := sorry

/-- The inverse total functor composes a fiber component with the selected cartesian lift. -/
@[simp]
theorem CoGrothendieck.inverse.map (χ : p.SplitCleavage)
    {X Y : Pseudofunctor.CoGrothendieck χ.toCatPresheaf.toPseudofunctor'} (f : X ⟶ Y) :
    (CoGrothendieck.inverse χ).map f =
      f.fiber.1 ≫ χ.toCleavage.cartesianHom f.base Y.fiber := sorry

/-- The explicit strict isomorphism over `C` between a split fibred category and the
co-Grothendieck construction of its strict fiber presheaf. -/
@[stacks 02XW "strict co-Grothendieck realization of split cleavage data"]
noncomputable def CoGrothendieck.StrictIso.apply (χ : p.SplitCleavage) :
    BasedCategory.StrictIso (BasedCategory.ofFunctor p)
      (BasedCategory.ofFunctor
        (Pseudofunctor.CoGrothendieck.forget χ.toCatPresheaf.toPseudofunctor')) where
  toIsoCat :=
    { functor := (CoGrothendieck.functor χ).toFunctor
      inverse := CoGrothendieck.inverse χ
      unit_eq := Implementation.unit χ
      counit_eq := Implementation.counit χ }
  functor_w := (CoGrothendieck.functor χ).w

/-- The forward based functor of the strict isomorphism is the explicit comparison owner. -/
@[simp]
theorem CoGrothendieck.StrictIso.hom (χ : p.SplitCleavage) :
    (CoGrothendieck.StrictIso.apply χ).hom = CoGrothendieck.functor χ := sorry

/-- The underlying inverse functor is the explicit witness-forgetting comparison. -/
@[simp]
theorem CoGrothendieck.StrictIso.inv.toFunctor (χ : p.SplitCleavage) :
    (CoGrothendieck.StrictIso.apply χ).inv.toFunctor =
      CoGrothendieck.inverse χ := sorry

/-- The inverse strict comparison forgets the fiber witness of an object. -/
@[simp, stacks 02XW "object formula for the inverse strict co-Grothendieck comparison"]
theorem CoGrothendieck.StrictIso.inv.obj (χ : p.SplitCleavage)
    (X : Pseudofunctor.CoGrothendieck χ.toCatPresheaf.toPseudofunctor') :
    (CoGrothendieck.StrictIso.apply χ).inv.toFunctor.obj X = X.fiber.1 := sorry

/-- The inverse comparison composes a fiber component with the selected cartesian lift. -/
@[simp, stacks 02XW "map formula for the inverse strict co-Grothendieck comparison"]
theorem CoGrothendieck.StrictIso.inv.map (χ : p.SplitCleavage)
    {X Y : Pseudofunctor.CoGrothendieck χ.toCatPresheaf.toPseudofunctor'} (f : X ⟶ Y) :
    (CoGrothendieck.StrictIso.apply χ).inv.toFunctor.map f =
      f.fiber.1 ≫ χ.toCleavage.cartesianHom f.base Y.fiber := sorry

end ComparisonImplementation

end Functor.SplitCleavage

end CategoryTheory
