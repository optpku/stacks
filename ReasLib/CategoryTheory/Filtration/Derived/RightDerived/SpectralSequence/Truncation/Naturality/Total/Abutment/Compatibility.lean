/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Naturality.Total.Compatibility
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Naturality.Total.Abutment
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Total.Abutment
import Mathlib.Tactic.CrossRefAttribute

/-!
# Compatibility of generic and truncation total abutments

The neutral and truncation total realizations have the same abutment source.  Their targets are
identified using the comparison isomorphisms already stored by the realization, so this bridge
does not choose a new representative of a derived object.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation.Realization.Total

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

/-- Naturality of the identity-valued source comparison for total truncation abutments. -/
@[reassoc, stacks 0BKM "naturality of the generic source comparison for total truncation abutments"]
theorem genericFunctor_abutmentSourceIso_naturality (n : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (genericFunctor F ⋙
          RightDerived.SpectralSequence.Realization.Total.abutmentSource F n).map m ≫
        (Iso.refl _).hom =
      (Iso.refl _).hom ≫ (abutmentSource F n).map m := sorry

/-- The generic abutment source after the truncation-to-generic functor is the specialized source. -/
@[stacks 0BKM "generic source comparison for total truncation abutments"]
noncomputable def genericFunctor_abutmentSourceIso (n : ℤ) :
    genericFunctor F ⋙
        RightDerived.SpectralSequence.Realization.Total.abutmentSource F n ≅
      abutmentSource F n :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun m => genericFunctor_abutmentSourceIso_naturality F n m)

/-- The generic cochain-level abutment target and the derived-category target are compared by
the stored generic and truncation abutment identifications. -/
@[stacks 0BKM "generic target comparison for total truncation abutments"]
noncomputable def genericFunctor_abutmentTargetIso (n : ℤ) :
    genericFunctor F ⋙
        RightDerived.SpectralSequence.Realization.Total.abutmentTarget F n ≅
      abutmentTarget F n :=
  (Functor.isoWhiskerLeft (genericFunctor F)
      (RightDerived.SpectralSequence.Realization.Total.abutmentComparison F n)).symm ≪≫
    genericFunctor_abutmentSourceIso F n ≪≫
    abutmentComparison F n

/-- A component of the generic-to-truncation abutment source comparison. -/
@[simp, stacks 0BKM "component of the generic source comparison for total truncation abutments"]
theorem genericFunctor_abutmentSourceIso_app (n : ℤ) (S : Realization.Total F) :
    (genericFunctor_abutmentSourceIso F n).app S = Iso.refl _ := sorry

/-- A component of the generic-to-truncation abutment target comparison. -/
@[simp, stacks 0BKM "component of the generic target comparison for total truncation abutments"]
theorem genericFunctor_abutmentTargetIso_app (n : ℤ) (S : Realization.Total F) :
    (genericFunctor_abutmentTargetIso F n).app S =
      (S.obj.original.targetIso n).symm ≪≫ S.obj.targetIso n := sorry

/-- The forward component of the generic-to-truncation abutment target comparison. -/
@[simp, stacks 0BKM "forward generic target comparison for total truncation abutments"]
theorem genericFunctor_abutmentTargetIso_hom_app (n : ℤ) (S : Realization.Total F) :
    (genericFunctor_abutmentTargetIso F n).hom.app S =
      (S.obj.original.targetIso n).inv ≫ (S.obj.targetIso n).hom := sorry

/-- The inverse component of the generic-to-truncation abutment target comparison. -/
@[simp, stacks 0BKM "inverse generic target comparison for total truncation abutments"]
theorem genericFunctor_abutmentTargetIso_inv_app (n : ℤ) (S : Realization.Total F) :
    (genericFunctor_abutmentTargetIso F n).inv.app S =
      (S.obj.targetIso n).inv ≫ (S.obj.original.targetIso n).hom := sorry

/-- Naturality of the forward generic-to-truncation abutment target comparison. -/
@[reassoc, stacks 0BKM
  "naturality of the forward generic target comparison for total truncation abutments"]
theorem genericFunctor_abutmentTargetIso_hom_naturality (n : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (genericFunctor F ⋙
          RightDerived.SpectralSequence.Realization.Total.abutmentTarget F n).map m ≫
        (genericFunctor_abutmentTargetIso F n).hom.app T =
      (genericFunctor_abutmentTargetIso F n).hom.app S ≫
        (abutmentTarget F n).map m := sorry

/-- Naturality of the inverse generic-to-truncation abutment target comparison. -/
@[reassoc, stacks 0BKM
  "naturality of the inverse generic target comparison for total truncation abutments"]
theorem genericFunctor_abutmentTargetIso_inv_naturality (n : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (abutmentTarget F n).map m ≫
        (genericFunctor_abutmentTargetIso F n).inv.app T =
      (genericFunctor_abutmentTargetIso F n).inv.app S ≫
        (genericFunctor F ⋙
          RightDerived.SpectralSequence.Realization.Total.abutmentTarget F n).map m := sorry

/-- Conjugating the specialized truncation abutment target map recovers the generic target map. -/
@[reassoc, stacks 0BKM "generic target-map computation for total truncation abutments"]
theorem genericFunctor_abutmentTargetIso_source_map (n : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (genericFunctor_abutmentTargetIso F n).hom.app S ≫
        (abutmentTarget F n).map m ≫
        (genericFunctor_abutmentTargetIso F n).inv.app T =
      (genericFunctor F ⋙
        RightDerived.SpectralSequence.Realization.Total.abutmentTarget F n).map m := sorry

/-- Conjugating the generic abutment target map recovers the specialized truncation target map. -/
@[reassoc, stacks 0BKM "specialized target-map computation for total truncation abutments"]
theorem genericFunctor_abutmentTargetIso_target_map (n : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (genericFunctor_abutmentTargetIso F n).inv.app S ≫
        (genericFunctor F ⋙
          RightDerived.SpectralSequence.Realization.Total.abutmentTarget F n).map m ≫
        (genericFunctor_abutmentTargetIso F n).hom.app T =
      (abutmentTarget F n).map m := sorry

/-- The generic and truncation abutment comparisons form a compatible square. -/
@[stacks 0BKM "compatibility of generic and truncation total abutments"]
theorem abutmentComparison_compat (n : ℤ) :
    Functor.isoWhiskerLeft (genericFunctor F)
          (RightDerived.SpectralSequence.Realization.Total.abutmentComparison F n) ≪≫
        genericFunctor_abutmentTargetIso F n =
      genericFunctor_abutmentSourceIso F n ≪≫ abutmentComparison F n := sorry

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation.Realization.Total
