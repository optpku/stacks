/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.CommFppf
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor
public import Mathlib.CategoryTheory.Monoidal.Braided.Transport

/-! # Coefficient transport and sheafification on the fppf and étale sites -/

@[expose] public section

open AlgebraicGeometry CategoryTheory SheafOfModules.RingedSite PresheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Identity-on-Γ comparison of the commutative étale structure presheaf with
the commutative fppf structure presheaf. -/
def commEtaleToFppfPresheaf (X : GroupoidsOver S) :
    (commEtaleStructureSheaf X).obj ⟶ (commAssociatedStructureSheaf X .fppf).obj where
  app := fun _ ↦ 𝟙 _
  naturality := fun _ _ _ ↦ sorry

/-- Restriction of scalars of a commutative fppf module to the commutative
étale structure presheaf, along `commEtaleToFppfPresheaf`. -/
def restrictToCommEtaleVal (X : GroupoidsOver S) (M : commAssociatedModules X .fppf) :
    PresheafOfModules.{u} (ringPresheaf (commEtaleStructureSheaf X).obj) :=
  (restrictScalars.{u} (presheafStructureMap (commEtaleToFppfPresheaf X))).obj M.val

/-- Restriction of scalars of a commutative fppf module presheaf to the
commutative étale structure presheaf, along `commEtaleToFppfPresheaf`. -/
def restrictPresheafToCommEtale (X : GroupoidsOver S)
    (M : PresheafOfModules.{u} (ringPresheaf (commAssociatedStructureSheaf X .fppf).obj)) :
    PresheafOfModules.{u} (ringPresheaf (commEtaleStructureSheaf X).obj) :=
  (restrictScalars.{u} (presheafStructureMap (commEtaleToFppfPresheaf X))).obj M

/-- `restrictToCommEtaleVal` is restriction of scalars of the underlying
presheaf. -/
theorem restrictToCommEtaleVal_eq (X : GroupoidsOver S) (M : commAssociatedModules X .fppf) :
    restrictToCommEtaleVal X M = restrictPresheafToCommEtale X M.val :=
  rfl

/-- View a commutative fppf module as an étale module by identity-on-Γ
restriction of scalars to `commEtaleStructureSheaf`. -/
def etaleOfCommRestrict {X : GroupoidsOver S} (M : commAssociatedModules X .fppf) :
    etaleModules X where
  val := restrictToCommEtaleVal X M
  isSheaf := sorry

/-- The morphism of étale views induced by a morphism of commutative fppf
modules. -/
def etaleOfCommRestrictMap {X : GroupoidsOver S} {M N : commAssociatedModules X .fppf}
    (f : M ⟶ N) :
    etaleOfCommRestrict M ⟶ etaleOfCommRestrict N where
  val :=
    (restrictScalars.{u} (presheafStructureMap (commEtaleToFppfPresheaf X))).map f.val

/-- The underlying presheaf morphism of `etaleOfCommRestrictMap` is restriction
of scalars of `f.val`. -/
theorem etaleOfCommRestrictMap_val {X : GroupoidsOver S}
    {M N : commAssociatedModules X .fppf} (f : M ⟶ N) :
    (etaleOfCommRestrictMap f).val =
      (restrictScalars.{u} (presheafStructureMap (commEtaleToFppfPresheaf X))).map
        f.val :=
  rfl

/-- Componentwise identity-restriction isomorphism for a commutative fppf
module presheaf. -/
def restrictPresheafToCommEtale_appIso {X : GroupoidsOver S}
    (M : PresheafOfModules.{u} (ringPresheaf (commAssociatedStructureSheaf X .fppf).obj))
    (U : X.totalᵒᵖ) :
    (restrictPresheafToCommEtale X M).obj U ≅ M.obj U :=
  (ModuleCat.restrictScalarsId'App
      ((presheafStructureMap (commEtaleToFppfPresheaf X)).app U).hom
      rfl (M.obj U)).symm

/-- Componentwise identity-restriction isomorphism for `restrictToCommEtaleVal`. -/
def restrictToCommEtaleVal_appIso {X : GroupoidsOver S} (M : commAssociatedModules X .fppf)
    (U : X.totalᵒᵖ) :
    (restrictToCommEtaleVal X M).obj U ≅ M.val.obj U :=
  restrictPresheafToCommEtale_appIso M.val U


/-- The commutative fppf module tensor uses original-universe sheafification. -/
instance commAssociatedFppfMonoidalCategory (X : GroupoidsOver S) :
    MonoidalCategory (commAssociatedModules X .fppf) :=
  @moduleMonoidalCategory.{u + 1, u, u} X.total inferInstance
    (X.associatedTopology .fppf)
    (associatedTopology_hasSheafCompose_commRing X .fppf)
    (associatedTopology_hasWeakSheafify X .fppf)
    (associatedTopology_wEqualsLocallyBijective X .fppf)
    (commAssociatedStructureSheaf X .fppf)

/-- The commutative fppf tensor is symmetric. -/
instance commAssociatedFppfSymmetricCategory (X : GroupoidsOver S) :
    SymmetricCategory (commAssociatedModules X .fppf) :=
  @moduleSymmetricCategory.{u + 1, u, u} X.total inferInstance
    (X.associatedTopology .fppf)
    (associatedTopology_hasSheafCompose_commRing X .fppf)
    (associatedTopology_hasWeakSheafify X .fppf)
    (associatedTopology_wEqualsLocallyBijective X .fppf)
    (commAssociatedStructureSheaf X .fppf)

/-- Fppf modules carry the tensor transported from commutative coefficients. -/
instance fppfModulesMonoidalCategory (X : GroupoidsOver S) :
    MonoidalCategory (RingedSite.ModuleCat.{u} (ringedSite X)) :=
  Monoidal.transport (commFppfModulesEquivalence X).symm

/-- Fppf module tensor products inherit the symmetry of commutative coefficients. -/
instance fppfModulesSymmetricCategory (X : GroupoidsOver S) :
    SymmetricCategory (RingedSite.ModuleCat.{u} (ringedSite X)) :=
  inferInstanceAs (SymmetricCategory
    (Monoidal.Transported (commFppfModulesEquivalence X).symm))

/-- Transport from commutative fppf coefficients preserves the unit and tensor. -/
instance fromCommFppfModules_monoidal (X : GroupoidsOver S) :
    (fromCommFppfModules X).Monoidal :=
  inferInstanceAs ((Monoidal.equivalenceTransported
    (commFppfModulesEquivalence X).symm).functor.Monoidal)

/-- Transport to commutative fppf coefficients preserves the unit and tensor. -/
instance toCommFppfModules_monoidal (X : GroupoidsOver S) :
    (toCommFppfModules X).Monoidal :=
  inferInstanceAs ((Monoidal.equivalenceTransported
    (commFppfModulesEquivalence X).symm).inverse.Monoidal)

variable {X : GroupoidsOver S}

/-- The fppf-to-étale coefficient comparison is the identity on sections. -/
def fppfCoefficientToEtale (X : GroupoidsOver S) :
    (commAssociatedStructureSheaf X .fppf).obj ⟶ (commEtaleStructureSheaf X).obj where
  app := fun _ => 𝟙 _
  naturality := by intros; rfl

/-- Regard an étale module presheaf as a module over the fppf structure
presheaf by the identity coefficient map; sections and restrictions are retained. -/
def fppfViewPresheaf (H : etaleModules X) :
    PresheafOfModules.{u} (ringPresheaf (commAssociatedStructureSheaf X .fppf).obj) :=
  (restrictScalars.{u} (presheafStructureMap (fppfCoefficientToEtale X))).obj H.val

/-- Equip the unchanged underlying module presheaf with its given fppf sheaf
property. The certificate changes no section data. -/
def fppfView (H : etaleModules X)
    (hH : Presheaf.IsSheaf (inheritedFppfTopology X) (fppfViewPresheaf H).presheaf) :
    commAssociatedModules X .fppf := ⟨fppfViewPresheaf H, hH⟩

/-- The identity section map from a presheaf to its successive étale and
fppf coefficient restrictions, using the explicit identity-restriction iso. -/
def reverseCoefficientUnit
    (P : PresheafOfModules.{u} (ringPresheaf (commAssociatedStructureSheaf X .fppf).obj)) :
    P ⟶ (restrictScalars.{u} (presheafStructureMap (fppfCoefficientToEtale X))).obj
      (restrictPresheafToCommEtale X P) where
  app U := (ModuleCat.restrictScalarsId'App
    (((presheafStructureMap (commEtaleToFppfPresheaf X)).app U).hom.comp
      ((presheafStructureMap (fppfCoefficientToEtale X)).app U).hom) rfl (P.obj U)).inv
  naturality := by intros; rfl

/-- Extend the given presheaf map uniquely across fppf sheafification into
an already fppf-sheaf target, after the two identity coefficient changes. -/
def fromFppfSheafification (H : etaleModules X)
    (hH : Presheaf.IsSheaf (inheritedFppfTopology X) (fppfViewPresheaf H).presheaf)
    (P : PresheafOfModules.{u} (ringPresheaf (commAssociatedStructureSheaf X .fppf).obj))
    (g : restrictPresheafToCommEtale X P ⟶ H.val) :
    (@moduleSheafification.{u + 1, u, u, u}
      X.total inferInstance (X.associatedTopology .fppf)
      (associatedTopology_hasSheafCompose_commRing X .fppf)
      (associatedTopology_hasWeakSheafify X .fppf)
      (associatedTopology_wEqualsLocallyBijective X .fppf)
      (commAssociatedStructureSheaf X .fppf)).obj P ⟶ fppfView H hH :=
  (@moduleSheafificationHomEquiv.{u + 1, u, u, u}
      X.total inferInstance (X.associatedTopology .fppf)
      (associatedTopology_hasSheafCompose_commRing X .fppf)
      (associatedTopology_hasWeakSheafify X .fppf)
      (associatedTopology_wEqualsLocallyBijective X .fppf)
      (commAssociatedStructureSheaf X .fppf) P (fppfView H hH)).symm
    (reverseCoefficientUnit P ≫
      (restrictScalars.{u} (presheafStructureMap (fppfCoefficientToEtale X))).map g)

/-- The constructed descent map is characterised by its original presheaf
map under the actual sheafification adjunction. -/
theorem fromFppfSheafification_homEquiv (H : etaleModules X)
    (hH : Presheaf.IsSheaf (inheritedFppfTopology X) (fppfViewPresheaf H).presheaf)
    (P : PresheafOfModules.{u} (ringPresheaf (commAssociatedStructureSheaf X .fppf).obj))
    (g : restrictPresheafToCommEtale X P ⟶ H.val) :
    (@moduleSheafificationHomEquiv.{u + 1, u, u, u}
      X.total inferInstance (X.associatedTopology .fppf)
      (associatedTopology_hasSheafCompose_commRing X .fppf)
      (associatedTopology_hasWeakSheafify X .fppf)
      (associatedTopology_wEqualsLocallyBijective X .fppf)
      (commAssociatedStructureSheaf X .fppf) P (fppfView H hH))
        (fromFppfSheafification H hH P g) =
      reverseCoefficientUnit P ≫
        (restrictScalars.{u} (presheafStructureMap (fppfCoefficientToEtale X))).map g :=
  Equiv.apply_symm_apply _ _

/-- The extension agrees with the specified presheaf map on sections coming
from the sheafification unit. Both coefficient changes are identity on sections. -/
theorem fromFppfSheafification_unit (H : etaleModules X)
    (hH : Presheaf.IsSheaf (inheritedFppfTopology X) (fppfViewPresheaf H).presheaf)
    (P : PresheafOfModules.{u} (ringPresheaf (commAssociatedStructureSheaf X .fppf).obj))
    (g : restrictPresheafToCommEtale X P ⟶ H.val) :
    @moduleSheafificationUnitToVal.{u + 1, u, u, u}
      X.total inferInstance (X.associatedTopology .fppf)
      (associatedTopology_hasSheafCompose_commRing X .fppf)
      (associatedTopology_hasWeakSheafify X .fppf)
      (associatedTopology_wEqualsLocallyBijective X .fppf)
      (commAssociatedStructureSheaf X .fppf) P ≫
        (fromFppfSheafification H hH P g).val =
      reverseCoefficientUnit P ≫
        (restrictScalars.{u} (presheafStructureMap (fppfCoefficientToEtale X))).map g := by
  calc
    _ = (@moduleSheafificationHomEquiv.{u + 1, u, u, u}
      X.total inferInstance (X.associatedTopology .fppf)
      (associatedTopology_hasSheafCompose_commRing X .fppf)
      (associatedTopology_hasWeakSheafify X .fppf)
      (associatedTopology_wEqualsLocallyBijective X .fppf)
      (commAssociatedStructureSheaf X .fppf) P (fppfView H hH))
          (fromFppfSheafification H hH P g) := by
      ext U x
      rfl
    _ = _ := fromFppfSheafification_homEquiv H hH P g

/-- The same modules after the two identity coefficient changes have the
identity section map. No inverse selected by an IsIso proof is used. -/
def etaleOfFppfViewToOriginal (H : etaleModules X)
    (hH : Presheaf.IsSheaf (inheritedFppfTopology X) (fppfViewPresheaf H).presheaf) :
    etaleOfCommRestrict (fppfView H hH) ⟶ H where
  val := { app := fun _ => 𝟙 _, naturality := by intros; rfl }

/-- Explicit reverse descent to a target which is already an fppf sheaf. -/
def descendToEtale (H : etaleModules X)
    (hH : Presheaf.IsSheaf (inheritedFppfTopology X) (fppfViewPresheaf H).presheaf)
    (P : PresheafOfModules.{u} (ringPresheaf (commAssociatedStructureSheaf X .fppf).obj))
    (g : restrictPresheafToCommEtale X P ⟶ H.val) :
    etaleOfCommRestrict ((@moduleSheafification.{u + 1, u, u, u}
      X.total inferInstance (X.associatedTopology .fppf)
      (associatedTopology_hasSheafCompose_commRing X .fppf)
      (associatedTopology_hasWeakSheafify X .fppf)
      (associatedTopology_wEqualsLocallyBijective X .fppf)
      (commAssociatedStructureSheaf X .fppf)).obj P) ⟶ H :=
  etaleOfCommRestrictMap (fromFppfSheafification H hH P g) ≫
    etaleOfFppfViewToOriginal H hH

/-- Étale descent is the restricted fppf sheafification extension followed
by the identity comparison back to the original étale target. -/
theorem descendToEtale_eq (H : etaleModules X)
    (hH : Presheaf.IsSheaf (inheritedFppfTopology X) (fppfViewPresheaf H).presheaf)
    (P : PresheafOfModules.{u} (ringPresheaf (commAssociatedStructureSheaf X .fppf).obj))
    (g : restrictPresheafToCommEtale X P ⟶ H.val) :
    descendToEtale H hH P g =
      etaleOfCommRestrictMap (fromFppfSheafification H hH P g) ≫
        etaleOfFppfViewToOriginal H hH := rfl

/-- The descended étale morphism has the prescribed value on every section
from the original presheaf. In particular, taking the pointwise tensor as `P`
fixes its values on pure tensors before sheafification. -/
theorem descendToEtale_unit (H : etaleModules X)
    (hH : Presheaf.IsSheaf (inheritedFppfTopology X) (fppfViewPresheaf H).presheaf)
    (P : PresheafOfModules.{u} (ringPresheaf (commAssociatedStructureSheaf X .fppf).obj))
    (g : restrictPresheafToCommEtale X P ⟶ H.val) :
    (restrictScalars.{u} (presheafStructureMap (commEtaleToFppfPresheaf X))).map
        (@moduleSheafificationUnitToVal.{u + 1, u, u, u}
      X.total inferInstance (X.associatedTopology .fppf)
      (associatedTopology_hasSheafCompose_commRing X .fppf)
      (associatedTopology_hasWeakSheafify X .fppf)
      (associatedTopology_wEqualsLocallyBijective X .fppf)
      (commAssociatedStructureSheaf X .fppf) P) ≫
        (descendToEtale H hH P g).val = g := by
  ext U x
  exact congrArg (fun k => k.app U x) (fromFppfSheafification_unit H hH P g)


end AlgebraicGeometry.GroupoidsOver
