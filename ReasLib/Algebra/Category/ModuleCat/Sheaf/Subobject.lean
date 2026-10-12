/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Sections of subobjects of module sheaves

This file owns the sectionwise image submodule attached to a subobject of an
arbitrary sheaf of modules.  It is independent of commutativity, ideal sheaves,
and any geometric realization of the site.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace SheafOfModules.Subobject

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}} {M : SheafOfModules.{z} R}

/-- The component of a module-sheaf subobject inclusion on an object of the site. -/
noncomputable abbrev inclusionApp
    (I : CategoryTheory.Subobject M) (U : Cᵒᵖ) :
    (I : SheafOfModules.{z} R).val.obj U ⟶ M.val.obj U :=
  (Hom.val I.arrow).app U

/-- The component of a subobject inclusion is injective on sections. -/
@[stacks 0GLY "injective section component"]
theorem inclusionApp_injective
    (I : CategoryTheory.Subobject M) (U : Cᵒᵖ) :
    Function.Injective (inclusionApp I U).hom := sorry

/-- The submodule of `M(U)` consisting of sections coming from the subobject `I`. -/
@[stacks 0GLY "module-subobject section image"]
noncomputable def sections
    (I : CategoryTheory.Subobject M) (U : Cᵒᵖ) :
    Submodule (R.obj.obj U) (M.val.obj U) :=
  LinearMap.range (inclusionApp I U).hom

/-- Sections of a module-sheaf subobject identify canonically with their image in the ambient
module of sections. -/
@[stacks 0GLY "module-subobject sections equivalence"]
noncomputable def sectionsIso
    (I : CategoryTheory.Subobject M) (U : Cᵒᵖ) :
    (I : SheafOfModules.{z} R).val.obj U ≅
      ModuleCat.of (R.obj.obj U) (sections I U) :=
  (LinearEquiv.ofInjective (inclusionApp I U).hom
    (inclusionApp_injective I U)).toModuleIso

/-- The forward map of `sectionsIso` is the subobject inclusion with codomain restricted to its
section image. -/
@[simp, stacks 0GLY "section-image equivalence specification"]
theorem sectionsIso_hom_apply
    (I : CategoryTheory.Subobject M) (U : Cᵒᵖ)
    (s : (I : SheafOfModules.{z} R).val.obj U) :
    (sectionsIso I U).hom s =
      ⟨inclusionApp I U s, LinearMap.mem_range_self (inclusionApp I U).hom s⟩ := sorry

/-- The forward section equivalence reads as the original subobject inclusion after coercion. -/
@[simp, stacks 0GLY "section-image coercion bridge"]
theorem sectionsIso_hom_coe
    (I : CategoryTheory.Subobject M) (U : Cᵒᵖ)
    (s : (I : SheafOfModules.{z} R).val.obj U) :
    ((sectionsIso I U).hom s : M.val.obj U) = inclusionApp I U s := sorry

/-- Membership in `sections I U` is witnessed by a section of the subobject over `U`. -/
theorem mem_sections
    (I : CategoryTheory.Subobject M) (U : Cᵒᵖ) (x : M.val.obj U) :
    x ∈ sections I U ↔
      ∃ s : (I : SheafOfModules.{z} R).val.obj U, inclusionApp I U s = x := sorry

/-- Every section of a module-sheaf subobject maps into its section image submodule. -/
theorem inclusionApp_mem_sections
    (I : CategoryTheory.Subobject M) (U : Cᵒᵖ)
    (s : (I : SheafOfModules.{z} R).val.obj U) :
    inclusionApp I U s ∈ sections I U := sorry

/-- The section image over `U` lies in the inverse image of the section image over `V`. -/
theorem sections_le_comap
    (I : CategoryTheory.Subobject M) {U V : Cᵒᵖ} (f : U ⟶ V) :
    sections I U ≤ Submodule.comap (M.val.restrictₛₗ f) (sections I V) := sorry

/-- Restricting a section belonging to a subobject section image preserves membership. -/
theorem map_mem_sections
    (I : CategoryTheory.Subobject M) {U V : Cᵒᵖ} (f : U ⟶ V)
    {x : M.val.obj U} (hx : x ∈ sections I U) :
    M.val.map f x ∈ sections I V := sorry

/-- Section image submodules are monotone in the module-sheaf subobject. -/
theorem sections_mono
    {I K : CategoryTheory.Subobject M} (h : I ≤ K) (U : Cᵒᵖ) :
    sections I U ≤ sections K U := sorry

/-- Taking the section image over a fixed object is a monotone operation on subobjects. -/
theorem sections_monotone (U : Cᵒᵖ) :
    Monotone (fun I : CategoryTheory.Subobject M ↦ sections I U) := sorry



end SheafOfModules.Subobject
