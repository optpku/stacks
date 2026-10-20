/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Groupoid
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic

/-!
# Fibers of categories fibred in groupoids

Groupoid structures on standard fibers and the converse fiberwise recognition API for the
intrinsic owner `Functor.IsFibered.InGroupoids`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor Functor.Fiber IsHomLift IsStronglyCartesian

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]

namespace Functor.IsFibered.InGroupoids

variable {p : S ⥤ C} [Functor.IsFibered.InGroupoids p]

/-- The inverse in a standard fiber is the actual Cartesian factor of the target identity
through the supplied vertical arrow. The Cartesian witness comes from the original
groupoid-fibration input, transported only along that arrow's given lift equation. -/
noncomputable def fiberInverse (U : C) {X Y : p.Fiber U} (φ : X ⟶ Y) : Y ⟶ X := by
  let cartesianAt : ∀ {R T : C} {a b : S} (f : R ⟶ T) (g : a ⟶ b),
      p.IsHomLift f g → p.IsCartesian f g := by
    intro R T a b f g h
    cases h
    exact Functor.IsFibered.InGroupoids.all_isCartesian g
  letI : p.IsHomLift (𝟙 U) φ.val := φ.property
  letI : p.IsHomLift (𝟙 U) (𝟙 Y.val) := IsHomLift.id Y.property
  letI : p.IsCartesian (𝟙 U) φ.val := cartesianAt _ _ φ.property
  exact ⟨IsCartesian.map p (𝟙 U) φ.val (𝟙 Y.val),
    IsCartesian.map_isHomLift p (𝟙 U) φ.val (𝟙 Y.val)⟩

/-- The specified Cartesian factor is a right inverse to the original fiber arrow. -/
@[simp]
theorem fiberInverse_comp (U : C) {X Y : p.Fiber U} (φ : X ⟶ Y) :
    fiberInverse U φ ≫ φ = 𝟙 Y := sorry

/-- Cartesian uniqueness gives the other inverse equation for those same actual maps. -/
@[simp]
theorem comp_fiberInverse (U : C) {X Y : p.Fiber U} (φ : X ⟶ Y) :
    φ ≫ fiberInverse U φ = 𝟙 X := sorry

/-- Every morphism in a standard fiber of a category fibred in groupoids is an isomorphism. -/
theorem hom_isIso (U : C) {X Y : p.Fiber U} (φ : X ⟶ Y) : IsIso φ :=
  ⟨⟨fiberInverse U φ, comp_fiberInverse U φ, fiberInverse_comp U φ⟩⟩

/-- Every standard fiber of a category fibred in groupoids is a groupoid. -/
instance fiberIsGroupoid (U : C) : IsGroupoid (p.Fiber U) where
  all_isIso φ := hom_isIso U φ

/-- Native groupoid promotion uses precisely the constructed Cartesian inverse. -/
@[simp]
theorem groupoid_inv_eq_fiberInverse (U : C) {X Y : p.Fiber U} (φ : X ⟶ Y) :
    @Groupoid.inv (p.Fiber U) (Groupoid.ofIsGroupoid) X Y φ = fiberInverse U φ := sorry

end Functor.IsFibered.InGroupoids

namespace Functor.IsFibered

/-- If a fibred functor has groupoid fibres, every total morphism is strongly Cartesian over its
image. -/
theorem isStronglyCartesian_of_fibersGroupoid
    {p : S ⥤ C} [p.IsFibered]
    (hfiber : ∀ U : C, IsGroupoid (p.Fiber U))
    {x y : S} (φ : x ⟶ y) :
    p.IsStronglyCartesian (p.map φ) φ := sorry

namespace InGroupoids

/-- A fibred functor whose standard fibres are groupoids is fibred in groupoids. -/
theorem of_isFibered_fibersGroupoid
    (p : S ⥤ C) (hp : p.IsFibered)
    (hfiber : ∀ U : C, IsGroupoid (p.Fiber U)) :
    Functor.IsFibered.InGroupoids p := sorry

/-- A functor is fibred in groupoids exactly when it is fibred and all its standard fibres are
groupoids. -/
theorem iff_isFibered_fibersGroupoid (p : S ⥤ C) :
    Functor.IsFibered.InGroupoids p ↔
      p.IsFibered ∧ ∀ U : C, IsGroupoid (p.Fiber U) := sorry

end InGroupoids
end Functor.IsFibered

end CategoryTheory
