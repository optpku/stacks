/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.LocallyQuasiCoherent
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module.Comparison
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.TopologyComparison

/-!
# Quasi-coherent modules and small-étale comparison morphisms

A module presheaf on a category fibred in groupoids is quasi-coherent exactly
when it is locally quasi-coherent and its small-étale comparisons are invertible.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- Ring-to-abelian-group sheaf composition exists on every slice of the étale
ringed site of a category fibred in groupoids. -/
instance hasSheafCompose_etaleRingedSite_over :
    ∀ x, ((etaleRingedSite X).siteTopology.over x).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  associatedTopology_over_hasSheafCompose X .etale

/-- Weak sheafification of abelian groups exists on every slice of the étale
ringed site of a category fibred in groupoids. -/
instance hasWeakSheafify_etaleRingedSite_over :
    ∀ x, HasWeakSheafify ((etaleRingedSite X).siteTopology.over x)
      AddCommGrpCat.{u} :=
  associatedTopology_over_hasWeakSheafify X .etale

/-- Sheafification equivalences on slices of the étale ringed site of a category
fibred in groupoids are exactly the locally bijective morphisms. -/
instance wEqualsLocallyBijective_etaleRingedSite_over :
    ∀ x, ((etaleRingedSite X).siteTopology.over x).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  associatedTopology_over_wEqualsLocallyBijective X .etale

set_option maxHeartbeats 1600000 in
/-- An étale sheaf of modules over the fppf structure presheaf, transported to
the étale structure presheaf by restriction of scalars. -/
def etaleModuleOfPresheaf
    (F : PresheafOfModules.{u} (structureSheaf X).obj)
    (hF : Presheaf.IsSheaf X.etaleTopology F.presheaf) : etaleModules X where
  val := (PresheafOfModules.restrictScalars (fppfToEtaleStructurePresheafIso X).inv).obj F
  isSheaf :=
    (Presheaf.isSheaf_of_iso_iff
      ((PresheafOfModules.restrictScalarsCompToPresheaf
        (fppfToEtaleStructurePresheafIso X).inv).app F)).2 hF

/-- Transport to the étale structure presheaf and back recovers the original
module presheaf. -/
theorem etaleModulePresheaf_etaleModuleOfPresheaf
    (F : PresheafOfModules.{u} (structureSheaf X).obj)
    (hF : Presheaf.IsSheaf X.etaleTopology F.presheaf) :
    etaleModulePresheaf (etaleModuleOfPresheaf F hF) = F := sorry

/-- An étale module is quasi-coherent if and only if it is locally
quasi-coherent and every canonical small-étale comparison is invertible. -/
theorem isQuasicoherent_iff_isLocallyQuasiCoherent (F : etaleModules X) :
    F.IsQuasicoherent ↔
      IsLocallyQuasiCoherent F ∧
        ∀ {x y : X.total} (φ : x ⟶ y), IsIso (moduleComparison φ F) := sorry

/-- The underlying fppf module presheaf of an étale module is quasi-coherent
if and only if it is locally quasi-coherent and every canonical small-étale
comparison is invertible. -/
theorem isQuasicoherentOn_fppf_iff_isLocallyQuasiCoherent (F : etaleModules X) :
    isQuasicoherentOn (etaleModulePresheaf F) .fppf ↔
      IsLocallyQuasiCoherent F ∧
        ∀ {x y : X.total} (φ : x ⟶ y), IsIso (moduleComparison φ F) := sorry

/-- Étale-site quasi-coherence of a module is equivalent to fppf
quasi-coherence of its underlying module presheaf. -/
theorem isQuasicoherent_iff_isQuasicoherentOn_fppf (F : etaleModules X) :
    F.IsQuasicoherent ↔ isQuasicoherentOn (etaleModulePresheaf F) .fppf := sorry

/-- A module presheaf is fppf quasi-coherent if and only if it is locally
quasi-coherent and every canonical small-étale pullback comparison along a
morphism of the total category is invertible. -/
theorem isQuasicoherentOn_fppf_iff_isLocallyQuasicoherent
    (F : PresheafOfModules.{u} (structureSheaf X).obj) :
    isQuasicoherentOn F .fppf ↔
      ∃ hF : IsLocallyQuasicoherent F,
        ∀ {x y : X.total} (φ : x ⟶ y),
          IsIso (moduleComparison φ (etaleModuleOfPresheaf F hF.isEtaleSheaf)) := sorry

/-- A locally quasi-coherent étale module whose canonical small-étale
comparisons are all invertible is quasi-coherent. -/
theorem isQuasicoherent_of_isLocallyQuasiCoherent (F : etaleModules X)
    [IsLocallyQuasiCoherent F]
    (h : ∀ {x y : X.total} (φ : x ⟶ y), IsIso (moduleComparison φ F)) :
    F.IsQuasicoherent := sorry

/-- A quasi-coherent étale module is locally quasi-coherent. -/
instance instIsLocallyQuasiCoherent_of_isQuasicoherent (F : etaleModules X)
    [F.IsQuasicoherent] : IsLocallyQuasiCoherent F := sorry

/-- Every canonical small-étale comparison of a quasi-coherent étale module
is invertible. -/
instance instModuleComparison_isIso_of_isQuasicoherent (F : etaleModules X)
    [F.IsQuasicoherent] {x y : X.total} (φ : x ⟶ y) :
    IsIso (moduleComparison φ F) := sorry

end AlgebraicGeometry.GroupoidsOver
