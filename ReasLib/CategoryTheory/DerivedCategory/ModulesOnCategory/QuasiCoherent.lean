/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat

/-!
# Quasi-coherent objects from derived restriction comparisons

This file owns the object property cut out by the invertibility of all derived restriction
comparison maps.  The construction is independent of a site presentation and is shared by the
ordinary and differential-graded modules-on-a-category settings.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe uC vC uD vD uE vE w z

namespace CategoryTheory.ModulesOnCategory

namespace QuasiCoherent

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {E : C → Type uE} [∀ U, Category.{vE} (E U)]
variable (RΓ : ∀ U : C, D ⥤ E U)
variable (restrict : ∀ {U V : C}, (U ⟶ V) → E V ⥤ E U)
variable
  (comparison : ∀ {U V : C} (f : U ⟶ V),
    RΓ V ⋙ restrict f ⟶ RΓ U)

/-- The comparison-isomorphism locus for a family of section functors and restriction functors.
This is the presentation-independent core of comparison-defined quasi-coherence. -/
@[stacks 0GYV "comparison-isomorphism locus", stacks 0GZ9 "comparison-isomorphism locus"]
def property : ObjectProperty D :=
  fun K ↦ ∀ ⦃U V : C⦄ (f : U ⟶ V), IsIso ((comparison f).app K)

/-- Membership in the comparison-isomorphism locus is pointwise invertibility of every
comparison map. -/
@[simp]
theorem mem_iff (K : D) :
    property RΓ restrict comparison K ↔
      ∀ ⦃U V : C⦄ (f : U ⟶ V), IsIso ((comparison f).app K) := sorry

/-- The full subcategory cut out by a family of comparison isomorphisms. -/
@[stacks 0GYV "comparison-defined full subcategory",
  stacks 0GZ9 "comparison-defined full subcategory"]
abbrev Objects := (property RΓ restrict comparison).FullSubcategory

/-- The underlying object of a comparison-defined object lies in the comparison-isomorphism
locus. -/
@[simp]
theorem obj_mem (K : Objects RΓ restrict comparison) :
    property RΓ restrict comparison K.obj := sorry

/-- Every comparison map attached to a comparison-defined object is an isomorphism. -/
theorem isIso_comparison (K : Objects RΓ restrict comparison)
    {U V : C} (f : U ⟶ V) :
    IsIso ((comparison f).app K.obj) := sorry

end QuasiCoherent

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
variable (RΓ : ∀ U : C, D ⥤ DerivedCategory (ModuleCat.{z, w} (𝒪.obj (op U))))
variable
  (restrict : ∀ {U V : C}, (U ⟶ V) →
    DerivedCategory (ModuleCat.{z, w} (𝒪.obj (op V))) ⥤
      DerivedCategory (ModuleCat.{z, w} (𝒪.obj (op U))))
variable
  (comparison : ∀ {U V : C} (f : U ⟶ V),
    RΓ V ⋙ restrict f ⟶ RΓ U)

/-- The object property consisting of objects whose derived restriction comparison is an
isomorphism for every arrow of the indexing category. This is the module-valued specialization
of `QuasiCoherent.property`. -/
@[stacks 0GYV, stacks 0GZ9]
def isQuasiCoherent : ObjectProperty D :=
  fun K ↦ ∀ ⦃U V : C⦄ (f : U ⟶ V), IsIso ((comparison f).app K)

/-- Membership in `isQuasiCoherent` is the pointwise invertibility of every comparison map. -/
@[simp]
theorem isQuasiCoherent_iff (K : D) :
    isQuasiCoherent 𝒪 RΓ restrict comparison K ↔
      ∀ ⦃U V : C⦄ (f : U ⟶ V), IsIso ((comparison f).app K) := sorry

/-- Definition 21.43.1 and Definition 24.33.1: `QC` is the full subcategory of objects whose
derived restriction comparison is an isomorphism for every arrow of the indexing category. -/
@[stacks 0GYV, stacks 0GZ9]
abbrev QC := (isQuasiCoherent 𝒪 RΓ restrict comparison).FullSubcategory

/-- The underlying object of an object of `QC` satisfies the comparison-isomorphism condition. -/
@[simp]
theorem qc_obj_isQuasiCoherent (K : QC 𝒪 RΓ restrict comparison) :
    isQuasiCoherent 𝒪 RΓ restrict comparison K.obj := sorry

/-- Every derived restriction comparison attached to an object of `QC` is an isomorphism. -/
theorem qc_isIso_comparison (K : QC 𝒪 RΓ restrict comparison)
    {U V : C} (f : U ⟶ V) :
    IsIso ((comparison f).app K.obj) := sorry

end CategoryTheory.ModulesOnCategory
