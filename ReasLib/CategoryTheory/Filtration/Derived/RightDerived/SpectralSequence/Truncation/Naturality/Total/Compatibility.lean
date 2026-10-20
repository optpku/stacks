/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Naturality.Total.PageTwo
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Total.Forget
import Mathlib.Tactic.CrossRefAttribute

/-!
# Compatibility of truncation total projections

The truncation specialization is dependent in its base object, but its generic realization views
are still obtained by canonical projection.  This leaf records those projection equalities as a
stable rewriting interface.
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

/-- The selected filtered-preimage projection is the generic base projection after `genericFunctor`. -/
@[stacks 0BKM "generic base projection of truncation total realizations"]
theorem genericFunctor_forgetBase :
    genericFunctor F ⋙
        RightDerived.SpectralSequence.Realization.Total.forgetBase F =
      forgetPreimage F := sorry

/-- The truncation filtered-model projection is the generic projection after `genericFunctor`. -/
@[stacks 0BKM "generic filtered projection of truncation total realizations"]
theorem genericFunctor_forgetFiltered :
    genericFunctor F ⋙
        RightDerived.SpectralSequence.Realization.Total.forgetFiltered F =
      forgetFiltered F := sorry

/-- The zero-based truncation sequence is the generic sequence projection after `genericFunctor`. -/
@[stacks 0BKM "generic original sequence projection of truncation total realizations"]
theorem genericFunctor_forgetOriginalSequence :
    genericFunctor F ⋙
        RightDerived.SpectralSequence.Realization.Total.forgetSequence F =
      forgetOriginalSequence F := sorry

/-- The truncation underlying-complex projection is the generic projection after `genericFunctor`. -/
@[stacks 0BKM "generic underlying projection of truncation total realizations"]
theorem genericFunctor_forgetUnderlying :
    genericFunctor F ⋙
        RightDerived.SpectralSequence.Realization.Total.forgetUnderlying F =
      forgetUnderlying F := sorry

/-- The neutral associated-spectral-sequence view agrees with generic associated data. -/
@[stacks 0BKM "generic associated projection of truncation total realizations"]
theorem genericFunctor_associatedFunctor :
    genericFunctor F ⋙
        RightDerived.SpectralSequence.Realization.Total.associatedFunctor F =
      associatedFunctor F := sorry

/-- Naturality of the identity comparison between the generic first-page entry at affine
bidegree `(-j, i + 2j)` and the specialized renumbered second-page entry at `(i, j)`. -/
@[stacks 0BKM "renumbered generic page source for total truncation realizations"]
theorem genericFunctor_pageTwoSourceIso_naturality (i : ℕ) (j : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (genericFunctor F ⋙
          RightDerived.SpectralSequence.Realization.Total.pageOneSource
            F (-j) (Int.ofNat i + 2 * j)).map m ≫
        (Iso.refl _).hom =
      (Iso.refl _).hom ≫ (pageTwoSource F i j).map m := sorry

/-- The standard renumbering identifies the generic first-page source at `(-j, i + 2j)` with
the specialized second-page source at `(i, j)`.  Its components are identities; only the
functorial map computation uses the renumbering law. -/
@[stacks 0BKM "renumbered generic page source for total truncation realizations"]
noncomputable def genericFunctor_pageTwoSourceIso (i : ℕ) (j : ℤ) :
    genericFunctor F ⋙
        RightDerived.SpectralSequence.Realization.Total.pageOneSource
          F (-j) (Int.ofNat i + 2 * j) ≅
      pageTwoSource F i j :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun m => genericFunctor_pageTwoSourceIso_naturality F i j m)

/-- Every component of the generic-to-renumbered source comparison is the identity
isomorphism. -/
@[simp, stacks 0BKM "component of the renumbered generic page source comparison"]
theorem genericFunctor_pageTwoSourceIso_app (i : ℕ) (j : ℤ)
    (S : Realization.Total F) :
    (genericFunctor_pageTwoSourceIso F i j).app S = Iso.refl _ := sorry

/-- The generic first-page target at affine bidegree `(-j, i + 2j)` and the specialized
second-page target are canonically isomorphic on total truncation realizations.  The
comparison is assembled from the renumbering and the two stored page identifications, so it
introduces no additional choice. -/
@[stacks 0BKM "generic target comparison for total truncation second pages"]
noncomputable def genericFunctor_pageTwoTargetIso (i : ℕ) (j : ℤ) :
    genericFunctor F ⋙
        RightDerived.SpectralSequence.Realization.Total.pageOneTarget
          F (-j) (Int.ofNat i + 2 * j) ≅
      pageTwoTarget F i j :=
  (Functor.isoWhiskerLeft (genericFunctor F)
      (RightDerived.SpectralSequence.Realization.Total.pageOneComparison
        F (-j) (Int.ofNat i + 2 * j))).symm ≪≫
    genericFunctor_pageTwoSourceIso F i j ≪≫
    pageTwoComparison F i j

/-- The target comparison component first inverts the generic first-page identification and
then applies the specialized second-page identification. -/
@[simp, stacks 0BKM "component of the generic target comparison for truncation second pages"]
theorem genericFunctor_pageTwoTargetIso_app (i : ℕ) (j : ℤ)
    (S : Realization.Total F) :
    (genericFunctor_pageTwoTargetIso F i j).app S =
      (S.obj.original.pageOneIso (-j) (Int.ofNat i + 2 * j)).symm ≪≫
        S.obj.pageTwoIso i j := sorry

/-- The forward target comparison first inverts the generic first-page identification and
then applies the specialized second-page identification. -/
@[simp, stacks 0BKM "forward generic target comparison for truncation second pages"]
theorem genericFunctor_pageTwoTargetIso_hom_app (i : ℕ) (j : ℤ)
    (S : Realization.Total F) :
    (genericFunctor_pageTwoTargetIso F i j).hom.app S =
      (S.obj.original.pageOneIso (-j) (Int.ofNat i + 2 * j)).inv ≫
        (S.obj.pageTwoIso i j).hom := sorry

/-- The inverse target comparison first inverts the specialized second-page identification
and then applies the generic first-page identification. -/
@[simp, stacks 0BKM "inverse generic target comparison for truncation second pages"]
theorem genericFunctor_pageTwoTargetIso_inv_app (i : ℕ) (j : ℤ)
    (S : Realization.Total F) :
    (genericFunctor_pageTwoTargetIso F i j).inv.app S =
      (S.obj.pageTwoIso i j).inv ≫
        (S.obj.original.pageOneIso (-j) (Int.ofNat i + 2 * j)).hom := sorry

/-- The generic-to-specialized target comparison is natural for total truncation-realization
morphisms. -/
@[reassoc, stacks 0BKM "naturality of the generic target comparison for truncation second pages"]
theorem genericFunctor_pageTwoTargetIso_hom_naturality (i : ℕ) (j : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (genericFunctor F ⋙
          RightDerived.SpectralSequence.Realization.Total.pageOneTarget
            F (-j) (Int.ofNat i + 2 * j)).map m ≫
        (genericFunctor_pageTwoTargetIso F i j).hom.app T =
      (genericFunctor_pageTwoTargetIso F i j).hom.app S ≫
        (pageTwoTarget F i j).map m := sorry

/-- The inverse generic-to-specialized target comparison is natural for total
truncation-realization morphisms. -/
@[reassoc, stacks 0BKM
  "inverse naturality of the generic target comparison for truncation second pages"]
theorem genericFunctor_pageTwoTargetIso_inv_naturality (i : ℕ) (j : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (pageTwoTarget F i j).map m ≫
        (genericFunctor_pageTwoTargetIso F i j).inv.app T =
      (genericFunctor_pageTwoTargetIso F i j).inv.app S ≫
        (genericFunctor F ⋙
          RightDerived.SpectralSequence.Realization.Total.pageOneTarget
            F (-j) (Int.ofNat i + 2 * j)).map m := sorry

/-- Conjugating the specialized second-page target map by the target comparison recovers the
generic first-page target map. -/
@[reassoc, stacks 0BKM "generic target-map computation for truncation second pages"]
theorem genericFunctor_pageTwoTargetIso_source_map (i : ℕ) (j : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (genericFunctor_pageTwoTargetIso F i j).hom.app S ≫
        (pageTwoTarget F i j).map m ≫
        (genericFunctor_pageTwoTargetIso F i j).inv.app T =
      (genericFunctor F ⋙
        RightDerived.SpectralSequence.Realization.Total.pageOneTarget
          F (-j) (Int.ofNat i + 2 * j)).map m := sorry

/-- Conjugating the generic first-page target map by the inverse target comparison recovers
the specialized second-page target map. -/
@[reassoc, stacks 0BKM "specialized target-map computation for truncation second pages"]
theorem genericFunctor_pageTwoTargetIso_target_map (i : ℕ) (j : ℤ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (genericFunctor_pageTwoTargetIso F i j).inv.app S ≫
        (genericFunctor F ⋙
          RightDerived.SpectralSequence.Realization.Total.pageOneTarget
            F (-j) (Int.ofNat i + 2 * j)).map m ≫
        (genericFunctor_pageTwoTargetIso F i j).hom.app T =
      (pageTwoTarget F i j).map m := sorry

/-- The generic first-page comparison, renumbering, and specialized second-page comparison
form the canonical compatibility square. -/
@[stacks 0BKM "compatibility of generic and specialized total truncation pages"]
theorem pageTwoComparison_compat (i : ℕ) (j : ℤ) :
    Functor.isoWhiskerLeft (genericFunctor F)
          (RightDerived.SpectralSequence.Realization.Total.pageOneComparison
            F (-j) (Int.ofNat i + 2 * j)) ≪≫
        genericFunctor_pageTwoTargetIso F i j =
      genericFunctor_pageTwoSourceIso F i j ≪≫
        pageTwoComparison F i j := sorry

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation.Realization.Total
