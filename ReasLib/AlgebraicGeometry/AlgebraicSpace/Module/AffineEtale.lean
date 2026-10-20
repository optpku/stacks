/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.EssentialImage
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.BaseChange
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AffineStructureSheaf
import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-coherent modules on the affine étale site of an algebraic space

This module packages the commutative structure presheaf, affine restriction, and
quasi-coherent comparison functors used to relate module presheaves on
`X_affine,étale` with quasi-coherent modules on an algebraic space `X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Presheaf Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineEtale

/-- The commutative global-sections presheaf on the affine étale site of an algebraic
space. -/
abbrev commStructurePresheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u} :=
  (affineEtaleToScheme X).op ⋙ Scheme.Γ

/-- The value of `commStructurePresheaf X` at an affine étale object is the
global-sections ring of the underlying scheme. -/
theorem commStructurePresheaf_obj {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : affineEtaleSite X) :
    (commStructurePresheaf X).obj (op U) = CommRingCat.of Γ(U.obj.left.left, ⊤) :=
  sorry

/-- The underlying ring presheaf of `affineStructureSheaf X` is obtained by
forgetting commutativity of `commStructurePresheaf X`. -/
theorem structurePresheaf_eq_ringPresheafOfComm {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineStructureSheaf X).obj = ringPresheafOfComm (commStructurePresheaf X) :=
  sorry

/-- Bundle a module presheaf on the affine étale site that satisfies the sheaf
condition as a sheaf of modules over `affineStructureSheaf X`. -/
def asSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : PresheafOfModules.{u} (ringPresheafOfComm (commStructurePresheaf X)))
    (hF : Presheaf.IsSheaf (affineEtaleTopology X) F.presheaf) :
    SheafOfModules (affineStructureSheaf X) :=
  ⟨F, hF⟩

/-- Forgetting the sheaf proof from `asSheaf` recovers the original module
presheaf after the canonical identification of structure presheaves. -/
theorem asSheaf_val {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : PresheafOfModules.{u} (ringPresheafOfComm (commStructurePresheaf X)))
    (hF : Presheaf.IsSheaf (affineEtaleTopology X) F.presheaf) :
    (asSheaf F hF).val = F :=
  sorry

/-- The canonical structure-ring map used to restrict module sheaves from
`X_étale` to `X_affine,étale`. Its underlying presheaf map is the identity. -/
def restrictionStructureMap {S : Scheme.{u}} (X : AlgebraicSpace S) :
    affineStructureSheaf X ⟶
      ((affineEtaleInclusion X).sheafPushforwardContinuous RingCat.{u}
        (affineEtaleTopology X) (smallEtaleTopology X)).obj (structureSheaf X) :=
  𝟙 _

/-- The affine restriction structure map is the identity on the restricted
structure sheaf. -/
theorem restrictionStructureMap_def {S : Scheme.{u}} (X : AlgebraicSpace S) :
    restrictionStructureMap X = 𝟙 _ :=
  sorry

/-- Restriction of module sheaves from the small étale site of `X` to its affine
étale subsite. -/
def restriction {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Modules X ⥤ SheafOfModules (affineStructureSheaf X) :=
  SheafOfModules.pushforward (restrictionStructureMap X)

/-- The underlying module presheaf of affine restriction is the canonical
pushforward along the identity structure map. -/
theorem restriction_obj_val {S : Scheme.{u}} {X : AlgebraicSpace S}
    (M : Modules X) :
    ((restriction X).obj M).val =
      (PresheafOfModules.pushforward (restrictionStructureMap X).hom).obj M.val :=
  sorry

/-- Affine restriction preserves quasi-coherence. -/
theorem restriction_mapsTo {S : Scheme.{u}} (X : AlgebraicSpace S) :
    SheafOfModules.isQuasicoherent (structureSheaf X) ≤
      (SheafOfModules.isQuasicoherent (affineStructureSheaf X)).inverseImage
        (restriction X) :=
  sorry

namespace restriction

/-- The restriction of a quasi-coherent module sheaf on `X` remains
quasi-coherent on the affine étale site. -/
instance objIsQuasicoherent {S : Scheme.{u}} {X : AlgebraicSpace S} (M : QCoh X) :
    ((restriction X).obj M.obj).IsQuasicoherent :=
  sorry

end restriction

/-- Restriction from quasi-coherent modules on `X` to quasi-coherent modules on
the affine étale site. -/
def qcRestriction {S : Scheme.{u}} (X : AlgebraicSpace S) :
    QCoh X ⥤ (SheafOfModules.isQuasicoherent (affineStructureSheaf X)).FullSubcategory :=
  ObjectProperty.FullSubcategory.restrict (restriction X) (restriction_mapsTo X)

/-- The object underlying affine quasi-coherent restriction is ordinary
module-sheaf restriction. -/
theorem qcRestriction_obj {S : Scheme.{u}} {X : AlgebraicSpace S} (M : QCoh X) :
    ((qcRestriction X).obj M).obj = (restriction X).obj M.obj :=
  sorry

namespace qcRestriction

/-- Restriction along the affine étale comparison is an equivalence on
quasi-coherent module sheaves. -/
instance isEquivalence {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (qcRestriction X).IsEquivalence :=
  sorry

end qcRestriction

/-- Objectwise base-change compatibility for a module presheaf on the affine
étale site: each adjoint transpose `F(U') ⊗_{𝒪_X(U')} 𝒪_X(U) ⟶ F(U)` is an
isomorphism. -/
abbrev baseChangeCompatible {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : PresheafOfModules.{u} (ringPresheafOfComm (commStructurePresheaf X))) : Prop :=
  PresheafOfModules.BaseChange.compatible (commStructurePresheaf X) F

/-- Base-change compatibility is the pointwise isomorphism condition on
`PresheafOfModules.BaseChange.map` along morphisms of the affine étale site. -/
theorem baseChangeCompatible_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : PresheafOfModules.{u} (ringPresheafOfComm (commStructurePresheaf X))) :
    baseChangeCompatible F ↔
      ∀ {U U' : affineEtaleSite X} (f : U ⟶ U'),
        IsIso (PresheafOfModules.BaseChange.map (commStructurePresheaf X) F f.op) :=
  sorry

/-- Quasi-coherence of a module presheaf on the ringed site
`(X_affine,étale, 𝒪_X)` in the sense of `SheafOfModules.IsQuasicoherent`. -/
def isQuasicoherent {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : PresheafOfModules.{u} (ringPresheafOfComm (commStructurePresheaf X))) : Prop :=
  ∃ hF : Presheaf.IsSheaf (affineEtaleTopology X) F.presheaf,
    (asSheaf F hF).IsQuasicoherent

/-- Quasi-coherence on the affine étale ringed site is sheafhood together with
`SheafOfModules.IsQuasicoherent`. -/
theorem isQuasicoherent_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : PresheafOfModules.{u} (ringPresheafOfComm (commStructurePresheaf X))) :
    isQuasicoherent F ↔
      ∃ hF : Presheaf.IsSheaf (affineEtaleTopology X) F.presheaf,
        (asSheaf F hF).IsQuasicoherent :=
  sorry

/-- Correspondence of an affine étale module presheaf with a quasi-coherent
module on `X` via the restriction functor `qcRestriction X`. -/
def correspondsToQuasiCoherent {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : PresheafOfModules.{u} (ringPresheafOfComm (commStructurePresheaf X))) : Prop :=
  ∃ (hF : Presheaf.IsSheaf (affineEtaleTopology X) F.presheaf)
      (hqc : (asSheaf F hF).IsQuasicoherent),
    (qcRestriction X).essImage ⟨asSheaf F hF, hqc⟩

/-- Correspondence via the affine étale comparison is essential-image membership
for `qcRestriction`. -/
theorem correspondsToQuasiCoherent_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : PresheafOfModules.{u} (ringPresheafOfComm (commStructurePresheaf X))) :
    correspondsToQuasiCoherent F ↔
      ∃ (hF : Presheaf.IsSheaf (affineEtaleTopology X) F.presheaf)
          (hqc : (asSheaf F hF).IsQuasicoherent),
        (qcRestriction X).essImage ⟨asSheaf F hF, hqc⟩ :=
  sorry

/-- Let `S` be a scheme, let `X` be an algebraic space over `S`, and
let `F` be a presheaf of `𝒪_X`-modules on `X_affine,étale`. The following are
equivalent: for every morphism `U ⟶ U'` of `X_affine,étale` the map
`F(U') ⊗_{𝒪_X(U')} 𝒪_X(U) ⟶ F(U)` is an isomorphism; `F` is a quasi-coherent
module on the ringed site `(X_affine,étale, 𝒪_X)` in the sense of
`SheafOfModules.IsQuasicoherent`; and `F` corresponds to a quasi-coherent module
on `X` via the restriction functor `qcRestriction X`. -/
@[stacks 0H04]
theorem quasicoherent_tfae {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : PresheafOfModules.{u} (ringPresheafOfComm (commStructurePresheaf X))) :
    List.TFAE [baseChangeCompatible F, isQuasicoherent F, correspondsToQuasiCoherent F] :=
  sorry

/-- Objectwise base-change compatibility is equivalent to quasi-coherence on the
affine étale ringed site. -/
theorem baseChangeCompatible_iff_isQuasicoherent {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : PresheafOfModules.{u} (ringPresheafOfComm (commStructurePresheaf X))) :
    baseChangeCompatible F ↔ isQuasicoherent F :=
  sorry

/-- Quasi-coherence on the affine étale ringed site is equivalent to correspondence
with a quasi-coherent module on `X`. -/
theorem isQuasicoherent_iff_correspondsToQuasiCoherent {S : Scheme.{u}}
    {X : AlgebraicSpace S}
    (F : PresheafOfModules.{u} (ringPresheafOfComm (commStructurePresheaf X))) :
    isQuasicoherent F ↔ correspondsToQuasiCoherent F :=
  sorry

/-- Objectwise base-change compatibility is equivalent to correspondence with a
quasi-coherent module on `X`. -/
theorem baseChangeCompatible_iff_correspondsToQuasiCoherent {S : Scheme.{u}}
    {X : AlgebraicSpace S}
    (F : PresheafOfModules.{u} (ringPresheafOfComm (commStructurePresheaf X))) :
    baseChangeCompatible F ↔ correspondsToQuasiCoherent F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.AffineEtale
