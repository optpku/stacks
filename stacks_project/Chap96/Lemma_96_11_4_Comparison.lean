/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.TopologyComparison
public import stacks_project.Chap96.Lemma_96_8_1_RingedSite

/-!
# Associated-site comparison of module presheaves

A presheaf of `𝒪_𝒳`-modules on a category fibred in groupoids may be viewed
on each associated ringed site `(𝒳_τ, 𝒪_𝒳)` by identity-on-Γ restriction of
scalars. Quasi-coherence in the sense of `SheafOfModules.IsQuasicoherent` is
then a property of that transported sheaf.
-/

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.GroupoidsOver

universe u

#check (AlgebraicGeometry.GroupoidsOver.associatedTopology_over_hasSheafCompose :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    (τ : StandardTopology),
    ∀ x, ((X.associatedTopology τ).over x).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}))

#check (AlgebraicGeometry.GroupoidsOver.associatedTopology_over_hasWeakSheafify :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    (τ : StandardTopology),
    ∀ x, HasWeakSheafify ((X.associatedTopology τ).over x) AddCommGrpCat.{u})

#check (AlgebraicGeometry.GroupoidsOver.associatedTopology_over_wEqualsLocallyBijective :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    (τ : StandardTopology),
    ∀ x, ((X.associatedTopology τ).over x).WEqualsLocallyBijective
      AddCommGrpCat.{u})

#check (AlgebraicGeometry.GroupoidsOver.associatedStructurePresheafIso :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (τ : StandardTopology),
    (structureSheaf X).obj ≅ (associatedStructureSheaf X τ).obj)

#check (AlgebraicGeometry.GroupoidsOver.associatedStructurePresheafIso_eq :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    (τ : StandardTopology),
    associatedStructurePresheafIso X τ =
      (X.p.sheafPushforwardContinuousCompSheafToPresheafIso RingCat.{u}
          (inheritedFppfTopology X) (Scheme.fppfTopology.over S)).app
        (StandardTopology.Big.structureSheaf .fppf S) ≪≫
        ((X.p.sheafPushforwardContinuousCompSheafToPresheafIso RingCat.{u}
            (X.associatedTopology τ) (τ.overTopology S)).app
          (StandardTopology.Big.structureSheaf τ S)).symm)

#check (AlgebraicGeometry.GroupoidsOver.associatedStructurePresheafIso_app :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    (τ : StandardTopology) (x : X.total),
    (associatedStructurePresheafIso X τ).hom.app (op x) = 𝟙 _)

#check (AlgebraicGeometry.GroupoidsOver.associatedToFppfStructurePresheaf :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    (τ : StandardTopology),
    (associatedStructureSheaf X τ).obj ⟶ (structureSheaf X).obj)

#check (AlgebraicGeometry.GroupoidsOver.associatedToFppfStructurePresheaf_eq :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    (τ : StandardTopology),
    associatedToFppfStructurePresheaf X τ =
      (associatedStructurePresheafIso X τ).inv)

#check (AlgebraicGeometry.GroupoidsOver.associatedToFppfStructurePresheaf_app :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    (τ : StandardTopology) (x : X.total),
    (associatedToFppfStructurePresheaf X τ).app (op x) = 𝟙 _)

#check (AlgebraicGeometry.GroupoidsOver.toAssociatedPresheaf :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    (F : PresheafOfModules.{u} (structureSheaf X).obj) (τ : StandardTopology),
    PresheafOfModules.{u} (associatedStructureSheaf X τ).obj)

#check (AlgebraicGeometry.GroupoidsOver.toAssociatedPresheaf_eq :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    (F : PresheafOfModules.{u} (structureSheaf X).obj) (τ : StandardTopology),
    toAssociatedPresheaf F τ =
      (PresheafOfModules.restrictScalars
        (associatedToFppfStructurePresheaf X τ)).obj F)

#check (AlgebraicGeometry.GroupoidsOver.toAssociatedPresheaf_presheaf :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    (F : PresheafOfModules.{u} (structureSheaf X).obj) (τ : StandardTopology),
    (toAssociatedPresheaf F τ).presheaf = F.presheaf)

#check (AlgebraicGeometry.GroupoidsOver.asAssociatedSheafOfModules :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    (F : PresheafOfModules.{u} (structureSheaf X).obj) (τ : StandardTopology)
    (h : Presheaf.IsSheaf (X.associatedTopology τ)
      (toAssociatedPresheaf F τ).presheaf),
    SheafOfModules.{u} (associatedStructureSheaf X τ))

#check (AlgebraicGeometry.GroupoidsOver.asAssociatedSheafOfModules_val :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    (F : PresheafOfModules.{u} (structureSheaf X).obj) (τ : StandardTopology)
    (h : Presheaf.IsSheaf (X.associatedTopology τ)
      (toAssociatedPresheaf F τ).presheaf),
    asAssociatedSheafOfModules F τ h = ⟨toAssociatedPresheaf F τ, h⟩)

#check (AlgebraicGeometry.GroupoidsOver.isQuasicoherentOn :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    (F : PresheafOfModules.{u} (structureSheaf X).obj) (τ : StandardTopology),
    Prop)

#check (AlgebraicGeometry.GroupoidsOver.isQuasicoherentOn_iff :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    (F : PresheafOfModules.{u} (structureSheaf X).obj) (τ : StandardTopology),
    isQuasicoherentOn F τ ↔
      ∃ h : Presheaf.IsSheaf (X.associatedTopology τ)
          (toAssociatedPresheaf F τ).presheaf,
        (asAssociatedSheafOfModules F τ h).IsQuasicoherent)

#check (AlgebraicGeometry.GroupoidsOver.isQuasicoherentOn_fppf_iff_isQuasicoherent :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    (F : PresheafOfModules.{u} (structureSheaf X).obj),
    isQuasicoherentOn F .fppf ↔
      ∃ h : Presheaf.IsSheaf (inheritedFppfTopology X) F.presheaf,
        @SheafOfModules.IsQuasicoherent _ _ _ _
          (associatedTopology_over_hasWeakSheafify X .fppf)
          (associatedTopology_over_wEqualsLocallyBijective X .fppf)
          (⟨F, h⟩ : SheafOfModules.{u} (structureSheaf X)))
