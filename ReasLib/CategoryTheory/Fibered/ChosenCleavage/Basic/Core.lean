/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.Cleavage.ReindexIso

/-!
# Choice-specialized reindexing core

This leaf exposes the selected reindexing functors, their cartesian arrows,
and their universal factorization API. The choice-free `Cleavage` API remains
the canonical owner; `Functor.Chosen` makes the selected cleavage explicit.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace Functor

/-- Reindexing along `f` for the cleavage selected from a fibred projection. The choice-free
owner is `Cleavage.reindex`. -/
@[stacks 02XN]
noncomputable def Chosen.reindex (p : S ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) : p.Fiber U ⥤ p.Fiber V :=
  (Cleavage.ofIsFibered p).reindex f

/-- The standard-fiber object selected by reindexing along `f` for the chosen cleavage. -/
noncomputable def Chosen.reindexObj (p : S ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) (x : p.Fiber U) : p.Fiber V :=
  (Cleavage.ofIsFibered p).reindexObj f x

/-- The morphism between selected reindexing objects forced by cartesian factorization. -/
noncomputable def Chosen.reindexMap (p : S ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) {x y : p.Fiber U} (φ : x ⟶ y) :
    Chosen.reindexObj p f x ⟶ Chosen.reindexObj p f y :=
  (Cleavage.ofIsFibered p).reindexMap f φ

/-- The selected strongly cartesian arrow underlying `Chosen.reindex`. -/
noncomputable def Chosen.cartesianHom (p : S ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) (x : p.Fiber U) :
    (Chosen.reindexObj p f x).1 ⟶ x.1 :=
  (Cleavage.ofIsFibered p).cartesianHom f x

/-- The selected arrow underlying `Chosen.reindex` is strongly cartesian over its base
arrow. -/
instance Chosen.cartesianHom.isStronglyCartesian (p : S ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) (x : p.Fiber U) :
    p.IsStronglyCartesian f (Chosen.cartesianHom p f x) := sorry

/-- The selected cartesian arrow is a lift of its displayed base arrow. -/
theorem Chosen.cartesianHom.isHomLift (p : S ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) (x : p.Fiber U) :
    p.IsHomLift f (Chosen.cartesianHom p f x) := sorry

/-- The image in the base of the selected cartesian arrow is its displayed base arrow, up to the
endpoint transports carried by the standard-fiber objects. -/
@[simp]
theorem Chosen.cartesianHom.map (p : S ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) (x : p.Fiber U) :
    p.map (Chosen.cartesianHom p f x) =
      eqToHom (Chosen.reindexObj p f x).2 ≫ f ≫ eqToHom x.2.symm := sorry

/-- The canonical factor of an ambient morphism through the cartesian arrow selected from a
fibred projection. -/
noncomputable def Chosen.cartesianFactor (p : S ⥤ C) [p.IsFibered]
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : p.Fiber U)
    {y : S} (φ : y ⟶ x.1) [p.IsHomLift (g ≫ f) φ] :
    y ⟶ (Chosen.reindexObj p f x).1 :=
  (Cleavage.ofIsFibered p).cartesianFactor f g x φ

/-- The canonical selected factor lies over the remaining base arrow. -/
instance Chosen.cartesianFactor.isHomLift (p : S ⥤ C) [p.IsFibered]
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : p.Fiber U)
    {y : S} (φ : y ⟶ x.1) [p.IsHomLift (g ≫ f) φ] :
    p.IsHomLift g (Chosen.cartesianFactor p f g x φ) := sorry

/-- The canonical selected factor has the prescribed composite with the selected cartesian
arrow. -/
@[simp, reassoc]
theorem Chosen.cartesianFactor.fac (p : S ⥤ C) [p.IsFibered]
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : p.Fiber U)
    {y : S} (φ : y ⟶ x.1) [p.IsHomLift (g ≫ f) φ] :
    Chosen.cartesianFactor p f g x φ ≫ Chosen.cartesianHom p f x = φ := sorry

/-- A selected factor with the correct base arrow and composite is the canonical one. -/
theorem Chosen.cartesianFactor.unique (p : S ⥤ C) [p.IsFibered]
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : p.Fiber U)
    {y : S} (φ : y ⟶ x.1) [p.IsHomLift (g ≫ f) φ]
    (ψ : y ⟶ (Chosen.reindexObj p f x).1) [p.IsHomLift g ψ]
    (hψ : ψ ≫ Chosen.cartesianHom p f x = φ) :
    ψ = Chosen.cartesianFactor p f g x φ := sorry

/-- The selected cartesian arrow is right-cancellative among ambient arrows over the same base
arrow. -/
theorem Chosen.cartesianHom.ambient_ext (p : S ⥤ C) [p.IsFibered]
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : p.Fiber U)
    {y : S} {φ ψ : y ⟶ (Chosen.reindexObj p f x).1}
    [p.IsHomLift g φ] [p.IsHomLift g ψ]
    (h : φ ≫ Chosen.cartesianHom p f x = ψ ≫ Chosen.cartesianHom p f x) :
    φ = ψ := sorry

/-- Universal-property form of `Chosen.cartesianFactor`. -/
theorem Chosen.cartesianFactor.existsUnique (p : S ⥤ C) [p.IsFibered]
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : p.Fiber U)
    {y : S} (φ : y ⟶ x.1) [p.IsHomLift (g ≫ f) φ] :
    ∃! ψ : y ⟶ (Chosen.reindexObj p f x).1,
      p.IsHomLift g ψ ∧ ψ ≫ Chosen.cartesianHom p f x = φ := sorry

/-- The selected reindexing target associated to an ambient morphism: reindex its codomain
along its image in the base. -/
@[stacks 02XN]
noncomputable def Chosen.verticalTarget (p : S ⥤ C) [p.IsFibered]
    {x y : S} (φ : x ⟶ y) : p.Fiber (p.obj x) :=
  (Cleavage.ofIsFibered p).reindexTarget φ

/-- The ambient vertical factor of a morphism through the selected cartesian arrow over its
image in the base. -/
noncomputable def Chosen.verticalFactorHom (p : S ⥤ C) [p.IsFibered]
    {x y : S} (φ : x ⟶ y) : x ⟶ (Chosen.verticalTarget p φ).1 :=
  (Cleavage.ofIsFibered p).verticalFactorHom φ

/-- The selected ambient factor lies over the identity of the source base object. -/
instance Chosen.verticalFactorHom.isHomLift (p : S ⥤ C) [p.IsFibered]
    {x y : S} (φ : x ⟶ y) :
    p.IsHomLift (𝟙 (p.obj x)) (Chosen.verticalFactorHom p φ) := sorry

/-- The vertical factor of an ambient morphism, bundled as a morphism in the standard fiber. -/
@[stacks 02XN]
noncomputable def Chosen.verticalFactor (p : S ⥤ C) [p.IsFibered]
    {x y : S} (φ : x ⟶ y) :
    (Fiber.mk (p := p) (a := x) rfl : p.Fiber (p.obj x)) ⟶
      Chosen.verticalTarget p φ :=
  (Cleavage.ofIsFibered p).verticalFactor φ

/-- The selected vertical factor followed by the selected cartesian arrow is the original
ambient morphism. -/
@[simp, reassoc]
theorem Chosen.verticalFactor.fac (p : S ⥤ C) [p.IsFibered]
    {x y : S} (φ : x ⟶ y) :
    (Chosen.verticalFactor p φ).1 ≫
      Chosen.cartesianHom p (p.map φ)
        (Fiber.mk (p := p) (a := y) rfl : p.Fiber (p.obj y)) =
      φ := sorry

/-- A vertical morphism with the selected cartesian factorization is the selected vertical
factor. -/
theorem Chosen.verticalFactor.unique (p : S ⥤ C) [p.IsFibered]
    {x y : S} (φ : x ⟶ y)
    (ψ : (Fiber.mk (p := p) (a := x) rfl : p.Fiber (p.obj x)) ⟶
      Chosen.verticalTarget p φ)
    (hψ : ψ.1 ≫ Chosen.cartesianHom p (p.map φ)
      (Fiber.mk (p := p) (a := y) rfl : p.Fiber (p.obj y)) = φ) :
    ψ = Chosen.verticalFactor p φ := sorry

/-- If an ambient morphism is strongly cartesian over its image in the base, then its selected
vertical factor is an isomorphism in the source fiber. -/
theorem Chosen.verticalFactor.isIso_of_isStronglyCartesian
    (p : S ⥤ C) [p.IsFibered] {x y : S} (φ : x ⟶ y)
    [p.IsStronglyCartesian (p.map φ) φ] :
    IsIso (Chosen.verticalFactor p φ) := sorry

/-- The object action of selected reindexing is the object selected by
`Cleavage.ofIsFibered`. -/
@[simp]
theorem Chosen.reindex.obj (p : S ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) (x : p.Fiber U) :
    (Chosen.reindex p f).obj x =
      Chosen.reindexObj p f x := sorry

/-- The morphism action of selected reindexing is the cartesian factorization selected by
`Cleavage.ofIsFibered`. -/
@[simp]
theorem Chosen.reindex.map (p : S ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) {x y : p.Fiber U} (φ : x ⟶ y) :
    (Chosen.reindex p f).map φ =
      Chosen.reindexMap p f φ := sorry

/-- The selected reindexing map is characterized by cartesian factorization. -/
@[reassoc]
theorem Chosen.reindexMap.fac (p : S ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) {x y : p.Fiber U} (φ : x ⟶ y) :
    (Chosen.reindexMap p f φ).1 ≫ Chosen.cartesianHom p f y =
      Chosen.cartesianHom p f x ≫ φ.1 := sorry

/-- A morphism between selected reindexing objects satisfying the cartesian factorization
equation is the selected reindexing map. -/
theorem Chosen.reindexMap.unique (p : S ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) {x y : p.Fiber U} (φ : x ⟶ y)
    (ψ : Chosen.reindexObj p f x ⟶ Chosen.reindexObj p f y)
    (h : ψ.1 ≫ Chosen.cartesianHom p f y =
      Chosen.cartesianHom p f x ≫ φ.1) :
    ψ = Chosen.reindexMap p f φ := sorry

/-- Selected reindexing on morphisms is characterized by the cartesian factorization
equation. -/
@[reassoc]
theorem Chosen.reindex.map_fac (p : S ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) {x y : p.Fiber U} (φ : x ⟶ y) :
    ((Chosen.reindex p f).map φ).1 ≫ Chosen.cartesianHom p f y =
      Chosen.cartesianHom p f x ≫ φ.1 := sorry

/-- Morphisms into a selected reindexing object are determined by their composite with the
selected strongly cartesian arrow. -/
theorem Chosen.cartesianHom.ext (p : S ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) {x : p.Fiber U} {y : p.Fiber V}
    {φ ψ : y ⟶ (Chosen.reindex p f).obj x}
    (h : φ.1 ≫ Chosen.cartesianHom p f x = ψ.1 ≫ Chosen.cartesianHom p f x) :
    φ = ψ := sorry

end Functor

end CategoryTheory
