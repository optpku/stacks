/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic

/-!
# Infinitesimal automorphisms in a category cofibered in groupoids

For a functor into a base category, this file defines the relative subgroup of fibre
automorphisms fixing a lifted morphism and the induced automorphism homomorphism along a
cocartesian lift.
-/

@[expose] public section

open CategoryTheory

universe uC uS vC vS

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]

namespace CategoryTheory.Functor

open Fiber

/-- The subgroup of automorphisms of `x'` whose fibre inclusion fixes the morphism `φ`. -/
noncomputable def infinitesimalAut (p : S ⥤ C)
    [IsFibered.InGroupoids p.op] {A' A : C} (f : A' ⟶ A)
    {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ] :
    Subgroup (Aut x') where
  carrier := {α | fiberInclusion.map α.hom ≫ φ = φ}
  mul_mem' := by
    intro α β hα hβ
    change fiberInclusion.map α.hom ≫ φ = φ at hα
    change fiberInclusion.map β.hom ≫ φ = φ at hβ
    change fiberInclusion.map (β.hom ≫ α.hom) ≫ φ = φ
    rw [Functor.map_comp, Category.assoc, hα, hβ]
  one_mem' := by
    change fiberInclusion.map (𝟙 x') ≫ φ = φ
    simp
  inv_mem' := by
    intro α hα
    change fiberInclusion.map α.hom ≫ φ = φ at hα
    change fiberInclusion.map α.inv ≫ φ = φ
    calc
      fiberInclusion.map α.inv ≫ φ =
          fiberInclusion.map α.inv ≫ (fiberInclusion.map α.hom ≫ φ) :=
        congrArg (fiberInclusion.map α.inv ≫ ·) hα.symm
      _ = φ := by
        rw [← Category.assoc, ← Functor.map_comp, α.inv_hom_id, Functor.map_id,
          Category.id_comp]

/-- Membership in `infinitesimalAut` is the equation obtained by composing with `φ`. -/
theorem mem_infinitesimalAut (p : S ⥤ C)
    [IsFibered.InGroupoids p.op] {A' A : C} (f : A' ⟶ A)
    {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    (α : Aut x') :
    α ∈ infinitesimalAut p f φ ↔ fiberInclusion.map α.hom ≫ φ = φ := Iff.rfl

set_option backward.isDefEq.respectTransparency false in
/-- The homomorphism on fibre automorphism groups induced by a cocartesian lift `φ`. -/
noncomputable def fiberAutHom (p : S ⥤ C)
    [IsFibered.InGroupoids p.op] {A' A : C} (f : A' ⟶ A)
    {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x)
    [p.IsHomLift f φ] [p.IsCocartesian f φ] :
    Aut x' →* Aut x where
  toFun α :=
    have h_hom : p.IsHomLift f (fiberInclusion.map α.hom ≫ φ) :=
      @CategoryTheory.IsHomLift.comp_lift_id_left _ _ _ _ p _ _ _ _ _ f φ _
        (fiberInclusion.map α.hom) α.hom.property
    have h_inv : p.IsHomLift f (fiberInclusion.map α.inv ≫ φ) :=
      @CategoryTheory.IsHomLift.comp_lift_id_left _ _ _ _ p _ _ _ _ _ f φ _
        (fiberInclusion.map α.inv) α.inv.property
    Fiber.isoMk
      { hom := @IsCocartesian.map _ _ _ _ p _ _ _ _ f φ _ _
          (fiberInclusion.map α.hom ≫ φ) h_hom
        inv := @IsCocartesian.map _ _ _ _ p _ _ _ _ f φ _ _
          (fiberInclusion.map α.inv ≫ φ) h_inv
        hom_inv_id := by
          letI := h_hom
          letI := h_inv
          refine @IsCocartesian.ext _ _ _ _ p _ _ _ _ f φ _ _ _ _
            (by infer_instance) (CategoryTheory.IsHomLift.id x.property) ?_
          rw [← Category.assoc, IsCocartesian.fac, Category.assoc,
            IsCocartesian.fac, ← Category.assoc, ← Functor.map_comp,
            α.hom_inv_id, Functor.map_id, Category.id_comp]
          exact (Category.comp_id φ).symm
        inv_hom_id := by
          letI := h_hom
          letI := h_inv
          refine @IsCocartesian.ext _ _ _ _ p _ _ _ _ f φ _ _ _ _
            (by infer_instance) (CategoryTheory.IsHomLift.id x.property) ?_
          rw [← Category.assoc, IsCocartesian.fac, Category.assoc,
            IsCocartesian.fac, ← Category.assoc, ← Functor.map_comp,
            α.inv_hom_id, Functor.map_id, Category.id_comp]
          exact (Category.comp_id φ).symm }
      (@IsCocartesian.map_isHomLift _ _ _ _ p _ _ _ _ f φ _ _
        (fiberInclusion.map α.hom ≫ φ) h_hom)
  map_one' := by
    apply Aut.ext
    apply Fiber.hom_ext
    change IsCocartesian.map p f φ (fiberInclusion.map (𝟙 x') ≫ φ) =
      fiberInclusion.map (𝟙 x)
    apply IsCocartesian.ext p f φ
    rw [IsCocartesian.fac]
    simp
  map_mul' := by
    intro α β
    apply Aut.ext
    apply Fiber.hom_ext
    change IsCocartesian.map p f φ (fiberInclusion.map (β.hom ≫ α.hom) ≫ φ) =
      IsCocartesian.map p f φ (fiberInclusion.map β.hom ≫ φ) ≫
        IsCocartesian.map p f φ (fiberInclusion.map α.hom ≫ φ)
    apply IsCocartesian.ext p f φ
    simp only [Functor.map_comp, IsCocartesian.fac, IsCocartesian.fac_assoc,
      Category.assoc]

/-- The induced automorphism is characterized by the commutative square for `φ`. -/
theorem fiberAutHom_comp (p : S ⥤ C)
    [IsFibered.InGroupoids p.op] {A' A : C} (f : A' ⟶ A)
    {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x)
    [p.IsHomLift f φ] [p.IsCocartesian f φ] (α : Aut x') :
    φ ≫ fiberInclusion.map (fiberAutHom p f φ α).hom =
      fiberInclusion.map α.hom ≫ φ := by
  change φ ≫ IsCocartesian.map p f φ (fiberInclusion.map α.hom ≫ φ) =
    fiberInclusion.map α.hom ≫ φ
  exact IsCocartesian.fac p f φ (fiberInclusion.map α.hom ≫ φ)

/-- Under cocartesianness, `infinitesimalAut` is the kernel of `fiberAutHom`. -/
theorem infinitesimalAut_eq_ker (p : S ⥤ C)
    [IsFibered.InGroupoids p.op] {A' A : C} (f : A' ⟶ A)
    {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x)
    [p.IsHomLift f φ] [p.IsCocartesian f φ] :
    infinitesimalAut p f φ = (fiberAutHom p f φ).ker := by
  apply Subgroup.ext
  intro α
  rw [mem_infinitesimalAut p f φ α, MonoidHom.mem_ker]
  constructor
  · intro hα
    apply Aut.ext
    apply Fiber.hom_ext
    apply IsCocartesian.ext p f φ
    rw [fiberAutHom_comp, hα]
    change φ = φ ≫ 𝟙 _
    exact (Category.comp_id φ).symm
  · intro hα
    rw [← fiberAutHom_comp p f φ α, hα]
    change φ ≫ 𝟙 _ = φ
    exact Category.comp_id φ

end CategoryTheory.Functor
