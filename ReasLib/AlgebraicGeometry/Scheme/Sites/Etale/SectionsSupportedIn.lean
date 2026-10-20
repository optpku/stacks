/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Submonoid.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AbelianSupport

/-!
# Étale sections supported in a subset

Supported sections form an additive subgroup, and restriction takes support
into the inverse image of the original support subset.
-/

public section

open CategoryTheory Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})

namespace SectionsSupportedIn

/-- The zero section has support contained in every subset. -/
private theorem zero_support_subset (U : X.Etale) (Z : Set U.left) :
    (abelianSheafSectionSupport F U 0 : Set U.left) ⊆ Z := sorry

/-- A sum of sections supported in a subset is supported in the same subset. -/
private theorem add_support_subset (U : X.Etale) (Z : Set U.left)
    (σ τ : F.1.obj (op U))
    (hσ : (abelianSheafSectionSupport F U σ : Set U.left) ⊆ Z)
    (hτ : (abelianSheafSectionSupport F U τ : Set U.left) ⊆ Z) :
    (abelianSheafSectionSupport F U (σ + τ) : Set U.left) ⊆ Z := sorry

/-- The negative of a section supported in a subset is supported in that subset. -/
private theorem neg_support_subset (U : X.Etale) (Z : Set U.left)
    (σ : F.1.obj (op U))
    (hσ : (abelianSheafSectionSupport F U σ : Set U.left) ⊆ Z) :
    (abelianSheafSectionSupport F U (-σ) : Set U.left) ⊆ Z := sorry

end SectionsSupportedIn

/-- The additive group of sections of an abelian sheaf `F` on an object `U` of
`X.Etale` whose étale section support is contained in `Z`. -/
def abelianSheafSectionsSupportedIn (U : X.Etale) (Z : Set U.left) :
    AddSubgroup (F.1.obj (op U)) where
  carrier := {σ | (abelianSheafSectionSupport F U σ : Set U.left) ⊆ Z}
  zero_mem' := SectionsSupportedIn.zero_support_subset F U Z
  add_mem' := fun {σ τ} hσ hτ => SectionsSupportedIn.add_support_subset F U Z σ τ hσ hτ
  neg_mem' := fun {σ} hσ => SectionsSupportedIn.neg_support_subset F U Z σ hσ

/-- Membership in supported étale sections is containment of étale section support. -/
theorem mem_abelianSheafSectionsSupportedIn_iff (U : X.Etale) (Z : Set U.left)
    (σ : F.1.obj (op U)) :
    σ ∈ abelianSheafSectionsSupportedIn F U Z ↔
      (abelianSheafSectionSupport F U σ : Set U.left) ⊆ Z := sorry

namespace SectionsSupportedIn

/-- Restriction of a supported section is supported in the inverse-image subset. -/
private theorem restrict_mem {U U' : X.Etale} (φ : U' ⟶ U) (Z : Set U.left)
    (σ : abelianSheafSectionsSupportedIn F U Z) :
    F.1.map φ.op σ.val ∈ abelianSheafSectionsSupportedIn F U' (φ.left ⁻¹' Z) := sorry

end SectionsSupportedIn

/-- Restriction of supported étale sections along a morphism of `X.Etale`. -/
def restrictSupportedIn {U U' : X.Etale} (φ : U' ⟶ U) (Z : Set U.left) :
    abelianSheafSectionsSupportedIn F U Z →+
      abelianSheafSectionsSupportedIn F U' (φ.left ⁻¹' Z) :=
  ((F.1.map φ.op).hom.restrict (abelianSheafSectionsSupportedIn F U Z)).codRestrict
    (abelianSheafSectionsSupportedIn F U' (φ.left ⁻¹' Z))
    (SectionsSupportedIn.restrict_mem F φ Z)

/-- Restriction of supported étale sections acts by the étale sheaf restriction map. -/
theorem restrictSupportedIn_apply {U U' : X.Etale} (φ : U' ⟶ U) (Z : Set U.left)
    (σ : abelianSheafSectionsSupportedIn F U Z) :
    (restrictSupportedIn F φ Z σ).val = F.1.map φ.op σ.val := sorry

end AlgebraicGeometry.Scheme.Etale

end
