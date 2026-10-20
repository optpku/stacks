/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Linear
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.CategoryTheory.Shift.ShiftedHom.ModuleCat

/-!
# Derived Ext over an affine base

A morphism `X ⟶ Spec A` equips shifted morphisms between derived `𝒪_X`-modules with the
`A`-module structure induced by its map on global sections.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.DerivedExt

variable {A : Type u} [CommRing A] {X : Scheme.{u}}

/-- The shifted-Hom bifunctor with its `A`-module structure induced by a morphism
`f : X ⟶ Spec A`. -/
noncomputable def bifunctor (f : X ⟶ Spec (CommRingCat.of A)) (n : ℤ) :
    (RingedSpace.ModuleDerived X.toRingedSpace)ᵒᵖ ⥤
      RingedSpace.ModuleDerived X.toRingedSpace ⥤ ModuleCat.{u + 1} A :=
  @CategoryTheory.ShiftedHom.linearCoyoneda A _
    (RingedSpace.ModuleDerived X.toRingedSpace) _ _
    (@DerivedCategory.instLinear A _ X.toRingedSpace.Modules _ _
      (Linear.ofRingMorphism
        ((RingedSpace.GlobalSections.centerHom X.toRingedSpace).comp
          (globalSectionsMap f))) _)
    _ n

/-- The `A`-module of degree-`n` derived extensions from `K` to `L`, with scalar action
induced by `f`. -/
noncomputable abbrev value (f : X ⟶ Spec (CommRingCat.of A))
    (K L : RingedSpace.ModuleDerived X.toRingedSpace) (n : ℤ) : ModuleCat.{u + 1} A :=
  ((bifunctor f n).obj (op K)).obj L

/-- Forgetting the `A`-action on `value f K L n` recovers the shifted-morphism group
`Ext⁽n⁾(K, L)`. -/
theorem value_forget (f : X ⟶ Spec (CommRingCat.of A))
    (K L : RingedSpace.ModuleDerived X.toRingedSpace) (n : ℤ) :
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).obj (value f K L n) =
      AddCommGrpCat.of (Ext⁽n⁾(K, L)) := sorry

end AlgebraicGeometry.Scheme.Hom.DerivedExt
