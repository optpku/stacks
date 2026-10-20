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
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

/-- Membership in `infinitesimalAut` is the equation obtained by composing with `φ`. -/
theorem mem_infinitesimalAut (p : S ⥤ C)
    [IsFibered.InGroupoids p.op] {A' A : C} (f : A' ⟶ A)
    {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    (α : Aut x') :
    α ∈ infinitesimalAut p f φ ↔ fiberInclusion.map α.hom ≫ φ = φ := sorry

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
        hom_inv_id := sorry
        inv_hom_id := sorry }
      (@IsCocartesian.map_isHomLift _ _ _ _ p _ _ _ _ f φ _ _
        (fiberInclusion.map α.hom ≫ φ) h_hom)
  map_one' := sorry
  map_mul' := sorry

/-- The induced automorphism is characterized by the commutative square for `φ`. -/
theorem fiberAutHom_comp (p : S ⥤ C)
    [IsFibered.InGroupoids p.op] {A' A : C} (f : A' ⟶ A)
    {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x)
    [p.IsHomLift f φ] [p.IsCocartesian f φ] (α : Aut x') :
    φ ≫ fiberInclusion.map (fiberAutHom p f φ α).hom =
      fiberInclusion.map α.hom ≫ φ := sorry

/-- Under cocartesianness, `infinitesimalAut` is the kernel of `fiberAutHom`. -/
theorem infinitesimalAut_eq_ker (p : S ⥤ C)
    [IsFibered.InGroupoids p.op] {A' A : C} (f : A' ⟶ A)
    {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x)
    [p.IsHomLift f φ] [p.IsCocartesian f φ] :
    infinitesimalAut p f φ = (fiberAutHom p f φ).ker := sorry

end CategoryTheory.Functor
