/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.GlueData
import Mathlib.Tactic.CrossRefAttribute

/-!
# Universal properties of categorical gluing data

This file exposes the outgoing mapping property of a glued object as a canonical equivalence.
It is usable in any category admitting the multicoequalizer associated to the gluing diagram.
-/

@[expose] public section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory.GlueData

variable {C : Type u} [Category.{v} C]
variable (D : GlueData C) [HasMulticoequalizer D.diagram]

/-- A family of maps from the charts of `D` to `Y` which agrees across every overlap. -/
@[stacks 01JB "compatible gluing family"]
def CompatibleFamily (Y : C) :=
  { φ : ∀ i, D.U i ⟶ Y //
    ∀ i j, D.f i j ≫ φ i = (D.t i j ≫ D.f j i) ≫ φ j }

/-- Descend a compatible family of maps from the charts to the glued object. -/
@[stacks 01JB "categorical gluing descent"]
noncomputable def desc (Y : C) (φ : ∀ i, D.U i ⟶ Y)
    (hφ : ∀ i j, D.f i j ≫ φ i = (D.t i j ≫ D.f j i) ≫ φ j) :
    D.glued ⟶ Y :=
  Multicoequalizer.desc D.diagram Y φ (fun ⟨i, j⟩ ↦ hφ i j)

/-- The descended map restricts to the prescribed map on every chart. -/
@[reassoc (attr := simp), stacks 01JB "gluing descent chart computation"]
theorem ι_desc (Y : C) (φ : ∀ i, D.U i ⟶ Y)
    (hφ : ∀ i j, D.f i j ≫ φ i = (D.t i j ≫ D.f j i) ≫ φ j) (i) :
    D.ι i ≫ D.desc Y φ hφ = φ i := sorry

/-- A map from the glued object with prescribed chart restrictions is the canonical descent. -/
@[stacks 01JB "gluing descent uniqueness"]
theorem desc_unique (Y : C) (φ : ∀ i, D.U i ⟶ Y)
    (hφ : ∀ i j, D.f i j ≫ φ i = (D.t i j ≫ D.f j i) ≫ φ j)
    (f : D.glued ⟶ Y) (hf : ∀ i, D.ι i ≫ f = φ i) :
    f = D.desc Y φ hφ := sorry

/-- A compatible family of maps from the charts descends uniquely to the glued object. -/
@[stacks 01JB "existence and uniqueness of gluing descent"]
theorem existsUnique_desc (Y : C) (φ : ∀ i, D.U i ⟶ Y)
    (hφ : ∀ i j, D.f i j ≫ φ i = (D.t i j ≫ D.f j i) ≫ φ j) :
    ∃! f : D.glued ⟶ Y, ∀ i, D.ι i ≫ f = φ i := sorry

/-- Restriction of a map from the glued object is compatible on every overlap. -/
@[stacks 01JB "gluing restriction compatibility"]
theorem restrict_compatible (Y : C) (f : D.glued ⟶ Y) :
    ∀ i j, D.f i j ≫ D.ι i ≫ f =
      (D.t i j ≫ D.f j i) ≫ D.ι j ≫ f := sorry

/-- Restrict a map from the glued object to a compatible family on its charts. -/
@[stacks 01JB "gluing restriction family"]
noncomputable def restrict (Y : C) (f : D.glued ⟶ Y) : D.CompatibleFamily Y :=
  ⟨fun i ↦ D.ι i ≫ f, D.restrict_compatible Y f⟩

/-- Descending the restrictions of a map recovers the original map. -/
@[stacks 01JB "gluing descent after restriction"]
theorem desc_restrict (Y : C) (f : D.glued ⟶ Y) :
    D.desc Y (D.restrict Y f).1 (D.restrict Y f).2 = f := sorry

/-- Restricting a descended compatible family recovers that family. -/
@[stacks 01JB "gluing restriction after descent"]
theorem restrict_desc (Y : C) (φ : D.CompatibleFamily Y) :
    D.restrict Y (D.desc Y φ.1 φ.2) = φ := sorry

/-- Descend a bundled compatible family, avoiding repeated projection of its compatibility proof. -/
@[stacks 01JB "bundled gluing descent"]
noncomputable def descFamily (Y : C) (φ : D.CompatibleFamily Y) : D.glued ⟶ Y :=
  D.desc Y φ.1 φ.2

/-- The bundled gluing descent restricts to the family on every chart. -/
@[reassoc (attr := simp), stacks 01JB "bundled gluing descent chart computation"]
theorem ι_descFamily (Y : C) (φ : D.CompatibleFamily Y) (i) :
    D.ι i ≫ D.descFamily Y φ = φ.1 i := sorry

/-- The bundled gluing descent is unique with the prescribed chart restrictions. -/
@[stacks 01JB "bundled gluing descent uniqueness"]
theorem descFamily_unique (Y : C) (φ : D.CompatibleFamily Y)
    (f : D.glued ⟶ Y) (hf : ∀ i, D.ι i ≫ f = φ.1 i) :
    f = D.descFamily Y φ := sorry

/-- Maps out of a glued object are canonically equivalent to compatible families of chart
maps. -/
@[stacks 01JB "categorical gluing descent equivalence"]
noncomputable def homEquiv (Y : C) :
    (D.glued ⟶ Y) ≃ D.CompatibleFamily Y where
  toFun := D.restrict Y
  invFun φ := D.descFamily Y φ
  left_inv := D.desc_restrict Y
  right_inv := D.restrict_desc Y

/-- The forward map of the gluing equivalence restricts a morphism to all charts. -/
@[simp, stacks 01JB "gluing equivalence restriction"]
theorem homEquiv_apply (Y : C) (f : D.glued ⟶ Y) :
    D.homEquiv Y f = D.restrict Y f := sorry

/-- The inverse map of the gluing equivalence descends a compatible family. -/
@[simp, stacks 01JB "gluing equivalence descent"]
theorem homEquiv_symm_apply (Y : C) (φ : D.CompatibleFamily Y) :
    (D.homEquiv Y).symm φ = D.descFamily Y φ := sorry

/-- Maps out of a glued object are determined by their restrictions to all charts. -/
@[ext, stacks 01JB "gluing restriction extensionality"]
theorem hom_ext {Y : C} {f g : D.glued ⟶ Y}
    (h : ∀ i, D.ι i ≫ f = D.ι i ≫ g) : f = g := sorry

end CategoryTheory.GlueData
