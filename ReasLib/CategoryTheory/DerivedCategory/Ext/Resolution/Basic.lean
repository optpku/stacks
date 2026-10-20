/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution
public import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.CategoryTheory.Preadditive.HomCongr

@[expose] public section

/-!
# Basic Ext computations from cochain-complex resolutions

This leaf owns the two model-independent additive equivalences used to compute derived extension
groups from a chosen cochain-complex injective or projective resolution.  The comparison is
factored into named computation maps in `Resolution.Computation`; this file only keeps the
canonical bundled equivalences for compatibility with existing callers.
-/

open CategoryTheory ComplexShape DerivedCategory HomotopyCategory
open scoped DerivedExt

noncomputable section

universe w v u

namespace CochainComplex

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

local notation "KQ" => HomotopyCategory.quotient 𝒜 (up ℤ)

namespace InjectiveResolution

variable {Y : CochainComplex 𝒜 ℤ}

/-- The localization isomorphism induced by shifting the comparison map of an injective
resolution. -/
@[stacks 06XR]
noncomputable def shiftedComparisonIso (I : InjectiveResolution Y) (i : ℤ) :
    Q.obj (Y⟦i⟧) ≅ Q.obj (I.complex⟦i⟧) :=
  asIso (Q.map (I.ι⟦i⟧'))

/-- The forward map of `shiftedComparisonIso` is the localized shifted comparison map. -/
@[simp, stacks 06XR]
theorem shiftedComparisonIso_hom (I : InjectiveResolution Y) (i : ℤ) :
    (shiftedComparisonIso I i).hom = Q.map (I.ι⟦i⟧') := sorry

/-- Stacks 06XR: an injective resolution computes the derived extension group from `X` to `Y` by
shifted Hom groups in the homotopy category. -/
@[stacks 06XR]
noncomputable def extAddEquiv (I : InjectiveResolution Y) (X : CochainComplex 𝒜 ℤ) (i : ℤ) :
    Ext⁽i⁾(Q.obj X, Q.obj Y) ≃+ Ext⁽i⁾((KQ).obj X, (KQ).obj I) :=
  let e₁ :
      Ext⁽i⁾(Q.obj X, Q.obj Y) ≃+ (Q.obj X ⟶ Q.obj (Y⟦i⟧)) :=
    Iso.homCongrAddEquiv (Iso.refl _) ((Q.commShiftIso i).app Y).symm
  let e₂ :
      (Q.obj X ⟶ Q.obj (Y⟦i⟧)) ≃+ (Q.obj X ⟶ Q.obj (I⟦i⟧)) :=
    Iso.homCongrAddEquiv (Iso.refl _) (shiftedComparisonIso I i)
  let hQhBijective :
      Function.Bijective
        (Qh.map : ((KQ).obj X ⟶ (KQ).obj (I⟦i⟧)) → _) :=
    IsKInjective.Qh_map_bijective ((KQ).obj X) (I⟦i⟧)
  let e₃ :
      (Q.obj X ⟶ Q.obj (I⟦i⟧)) ≃+ ((KQ).obj X ⟶ (KQ).obj (I⟦i⟧)) :=
    (AddEquiv.ofBijective
        (Qh.mapAddHom : ((KQ).obj X ⟶ (KQ).obj (I⟦i⟧)) →+ _)
        hQhBijective).symm
  let e₄ :
      ((KQ).obj X ⟶ (KQ).obj (I⟦i⟧)) ≃+ Ext⁽i⁾((KQ).obj X, (KQ).obj I) :=
    Iso.homCongrAddEquiv (Iso.refl _) (((quotient 𝒜 (up ℤ)).commShiftIso i).app I)
  (e₁.trans (e₂.trans e₃)).trans e₄

end InjectiveResolution

namespace ProjectiveResolution

variable {X : CochainComplex 𝒜 ℤ}

/-- The localization isomorphism induced by the comparison map of a projective resolution. -/
@[stacks 06XR]
noncomputable def comparisonIso (P : ProjectiveResolution X) :
    Q.obj P.complex ≅ Q.obj X :=
  asIso (Q.map P.π)

/-- The forward map of `comparisonIso` is the localized projective comparison map. -/
@[simp, stacks 06XR]
theorem comparisonIso_hom (P : ProjectiveResolution X) :
    (comparisonIso P).hom = Q.map P.π := sorry

/-- Stacks 06XR: a projective resolution computes the derived extension group from `X` to `Y` by
shifted Hom groups in the homotopy category. -/
@[stacks 06XR]
noncomputable def extAddEquiv (P : ProjectiveResolution X) (Y : CochainComplex 𝒜 ℤ) (i : ℤ) :
    Ext⁽i⁾(Q.obj X, Q.obj Y) ≃+ Ext⁽i⁾((KQ).obj P, (KQ).obj Y) :=
  let e₁ :
      Ext⁽i⁾(Q.obj X, Q.obj Y) ≃+ (Q.obj X ⟶ Q.obj (Y⟦i⟧)) :=
    Iso.homCongrAddEquiv (Iso.refl _) ((Q.commShiftIso i).app Y).symm
  let e₂ :
      (Q.obj X ⟶ Q.obj (Y⟦i⟧)) ≃+ (Q.obj P ⟶ Q.obj (Y⟦i⟧)) :=
    Iso.homCongrAddEquiv (comparisonIso P).symm (Iso.refl _)
  let hQhBijective :
      Function.Bijective
        (Qh.map : ((KQ).obj P ⟶ (KQ).obj (Y⟦i⟧)) → _) :=
    IsKProjective.Qh_map_bijective (P : CochainComplex 𝒜 ℤ) ((KQ).obj (Y⟦i⟧))
  let e₃ :
      (Q.obj P ⟶ Q.obj (Y⟦i⟧)) ≃+ ((KQ).obj P ⟶ (KQ).obj (Y⟦i⟧)) :=
    (AddEquiv.ofBijective
        (Qh.mapAddHom : ((KQ).obj P ⟶ (KQ).obj (Y⟦i⟧)) →+ _)
        hQhBijective).symm
  let e₄ :
      ((KQ).obj P ⟶ (KQ).obj (Y⟦i⟧)) ≃+ Ext⁽i⁾((KQ).obj P, (KQ).obj Y) :=
    Iso.homCongrAddEquiv (Iso.refl _) (((quotient 𝒜 (up ℤ)).commShiftIso i).app Y)
  (e₁.trans (e₂.trans e₃)).trans e₄

end ProjectiveResolution

end

end CochainComplex
