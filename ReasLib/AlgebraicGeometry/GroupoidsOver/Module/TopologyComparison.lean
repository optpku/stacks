/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.GroupoidsOver.AssociatedStructureSheaf
public import ReasLib.AlgebraicGeometry.GroupoidsOver.StructureSheaf
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Projection

/-!
# Associated-site comparison of module presheaves

A presheaf of `𝒪_𝒳`-modules on a category fibred in groupoids may be viewed
on each associated ringed site `(𝒳_τ, 𝒪_𝒳)` by identity-on-Γ restriction of
scalars. Quasi-coherence in the sense of `SheafOfModules.IsQuasicoherent` is
then a property of that transported sheaf.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Ring-to-abelian-group sheaf composition exists on every slice of an
associated `τ`-topology. -/
instance associatedTopology_over_hasSheafCompose (X : GroupoidsOver S)
    (τ : StandardTopology) :
    ∀ x, ((X.associatedTopology τ).over x).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  sorry

/-- Weak sheafification of abelian groups exists on every slice of an associated
`τ`-topology. -/
instance associatedTopology_over_hasWeakSheafify (X : GroupoidsOver S)
    (τ : StandardTopology) :
    ∀ x, HasWeakSheafify ((X.associatedTopology τ).over x) AddCommGrpCat.{u} :=
  sorry

/-- Sheafification equivalences on slices of an associated `τ`-topology are
exactly the locally bijective morphisms. -/
instance associatedTopology_over_wEqualsLocallyBijective (X : GroupoidsOver S)
    (τ : StandardTopology) :
    ∀ x, ((X.associatedTopology τ).over x).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  sorry

/-- Identity-on-Γ comparison of the fppf structure presheaf `𝒪_𝒳` with the
associated `τ`-structure presheaf. -/
def associatedStructurePresheafIso (X : GroupoidsOver S) (τ : StandardTopology) :
    (structureSheaf X).obj ≅ (associatedStructureSheaf X τ).obj :=
  (X.p.sheafPushforwardContinuousCompSheafToPresheafIso RingCat.{u}
      (inheritedFppfTopology X) (Scheme.fppfTopology.over S)).app
    (StandardTopology.Big.structureSheaf .fppf S) ≪≫
    ((X.p.sheafPushforwardContinuousCompSheafToPresheafIso RingCat.{u}
        (X.associatedTopology τ) (τ.overTopology S)).app
      (StandardTopology.Big.structureSheaf τ S)).symm

/-- `associatedStructurePresheafIso` is the composite of the two continuous
pushforward identifications with the big structure presheaves. -/
theorem associatedStructurePresheafIso_eq (X : GroupoidsOver S)
    (τ : StandardTopology) :
    associatedStructurePresheafIso X τ =
      (X.p.sheafPushforwardContinuousCompSheafToPresheafIso RingCat.{u}
          (inheritedFppfTopology X) (Scheme.fppfTopology.over S)).app
        (StandardTopology.Big.structureSheaf .fppf S) ≪≫
        ((X.p.sheafPushforwardContinuousCompSheafToPresheafIso RingCat.{u}
            (X.associatedTopology τ) (τ.overTopology S)).app
          (StandardTopology.Big.structureSheaf τ S)).symm :=
  sorry

/-- Components of `associatedStructurePresheafIso` are identities of global
sections. -/
theorem associatedStructurePresheafIso_app (X : GroupoidsOver S)
    (τ : StandardTopology) (x : X.total) :
    (associatedStructurePresheafIso X τ).hom.app (op x) = 𝟙 _ :=
  sorry

/-- The coefficient morphism from the associated `τ`-structure presheaf to the
fppf structure presheaf, identity on global sections. -/
def associatedToFppfStructurePresheaf (X : GroupoidsOver S)
    (τ : StandardTopology) :
    (associatedStructureSheaf X τ).obj ⟶ (structureSheaf X).obj :=
  (associatedStructurePresheafIso X τ).inv

/-- `associatedToFppfStructurePresheaf` is the inverse of
`associatedStructurePresheafIso`. -/
theorem associatedToFppfStructurePresheaf_eq (X : GroupoidsOver S)
    (τ : StandardTopology) :
    associatedToFppfStructurePresheaf X τ =
      (associatedStructurePresheafIso X τ).inv :=
  sorry

/-- Components of `associatedToFppfStructurePresheaf` are identities of global
sections. -/
theorem associatedToFppfStructurePresheaf_app (X : GroupoidsOver S)
    (τ : StandardTopology) (x : X.total) :
    (associatedToFppfStructurePresheaf X τ).app (op x) = 𝟙 _ :=
  sorry

/-- Transport of a presheaf of `𝒪_𝒳`-modules to the associated `τ`-structure
presheaf by restriction of scalars along `associatedToFppfStructurePresheaf`. -/
def toAssociatedPresheaf {X : GroupoidsOver S}
    (F : PresheafOfModules.{u} (structureSheaf X).obj) (τ : StandardTopology) :
    PresheafOfModules.{u} (associatedStructureSheaf X τ).obj :=
  (PresheafOfModules.restrictScalars (associatedToFppfStructurePresheaf X τ)).obj F

/-- `toAssociatedPresheaf F τ` is restriction of scalars of `F` along
`associatedToFppfStructurePresheaf`. -/
theorem toAssociatedPresheaf_eq {X : GroupoidsOver S}
    (F : PresheafOfModules.{u} (structureSheaf X).obj) (τ : StandardTopology) :
    toAssociatedPresheaf F τ =
      (PresheafOfModules.restrictScalars
        (associatedToFppfStructurePresheaf X τ)).obj F :=
  sorry

/-- Restriction of scalars along `associatedToFppfStructurePresheaf` does not
change the underlying abelian presheaf. -/
theorem toAssociatedPresheaf_presheaf {X : GroupoidsOver S}
    (F : PresheafOfModules.{u} (structureSheaf X).obj) (τ : StandardTopology) :
    (toAssociatedPresheaf F τ).presheaf = F.presheaf :=
  sorry

/-- Package a sheaf of `𝒪_𝒳`-modules on the associated `τ`-site. -/
def asAssociatedSheafOfModules {X : GroupoidsOver S}
    (F : PresheafOfModules.{u} (structureSheaf X).obj) (τ : StandardTopology)
    (h : Presheaf.IsSheaf (X.associatedTopology τ)
      (toAssociatedPresheaf F τ).presheaf) :
    SheafOfModules.{u} (associatedStructureSheaf X τ) :=
  ⟨toAssociatedPresheaf F τ, h⟩

/-- The underlying module presheaf of `asAssociatedSheafOfModules` is
`toAssociatedPresheaf`. -/
theorem asAssociatedSheafOfModules_val {X : GroupoidsOver S}
    (F : PresheafOfModules.{u} (structureSheaf X).obj) (τ : StandardTopology)
    (h : Presheaf.IsSheaf (X.associatedTopology τ)
      (toAssociatedPresheaf F τ).presheaf) :
    asAssociatedSheafOfModules F τ h = ⟨toAssociatedPresheaf F τ, h⟩ :=
  sorry

/-- The module presheaf is a sheaf on the associated `τ`-site, and the
resulting module sheaf is quasi-coherent. -/
def isQuasicoherentOn {X : GroupoidsOver S}
    (F : PresheafOfModules.{u} (structureSheaf X).obj) (τ : StandardTopology) :
    Prop :=
  ∃ h : Presheaf.IsSheaf (X.associatedTopology τ)
      (toAssociatedPresheaf F τ).presheaf,
    (asAssociatedSheafOfModules F τ h).IsQuasicoherent

/-- Unfolding of `isQuasicoherentOn` as a sheaf witness together with
quasi-coherence on the associated `τ`-site. -/
theorem isQuasicoherentOn_iff {X : GroupoidsOver S}
    (F : PresheafOfModules.{u} (structureSheaf X).obj) (τ : StandardTopology) :
    isQuasicoherentOn F τ ↔
      ∃ h : Presheaf.IsSheaf (X.associatedTopology τ)
          (toAssociatedPresheaf F τ).presheaf,
        (asAssociatedSheafOfModules F τ h).IsQuasicoherent :=
  sorry

/-- Quasi-coherence on the associated fppf site is equivalent to sheafhood
and quasi-coherence of the original module presheaf on the fppf ringed site. -/
theorem isQuasicoherentOn_fppf_iff_isQuasicoherent {X : GroupoidsOver S}
    (F : PresheafOfModules.{u} (structureSheaf X).obj) :
    isQuasicoherentOn F .fppf ↔
      ∃ h : Presheaf.IsSheaf (inheritedFppfTopology X) F.presheaf,
        @SheafOfModules.IsQuasicoherent _ _ _ _
          (associatedTopology_over_hasWeakSheafify X .fppf)
          (associatedTopology_over_wEqualsLocallyBijective X .fppf)
          (⟨F, h⟩ : SheafOfModules.{u} (structureSheaf X)) :=
  sorry

variable (X : GroupoidsOver S)
variable (F : PresheafOfModules.{u} (structureSheaf X).obj)

/-- For a module presheaf on a category fibred in groupoids over a scheme,
quasi-coherence as a module sheaf is equivalent for the associated Zariski,
étale, and fppf topologies. -/
theorem isQuasicoherentOn_zariski_iff_etale_iff_fppf :
    List.TFAE [isQuasicoherentOn F .zariski, isQuasicoherentOn F .etale,
      isQuasicoherentOn F .fppf] :=
  sorry

/-- Quasi-coherence on the associated Zariski site is equivalent to
quasi-coherence on the associated étale site. -/
theorem isQuasicoherentOn_zariski_iff_etale :
    isQuasicoherentOn F .zariski ↔ isQuasicoherentOn F .etale :=
  sorry

/-- Quasi-coherence on the associated étale site is equivalent to
quasi-coherence on the associated fppf site. -/
theorem isQuasicoherentOn_etale_iff_fppf :
    isQuasicoherentOn F .etale ↔ isQuasicoherentOn F .fppf :=
  sorry

/-- Quasi-coherence on the associated Zariski site is equivalent to
quasi-coherence on the associated fppf site. -/
theorem isQuasicoherentOn_zariski_iff_fppf :
    isQuasicoherentOn F .zariski ↔ isQuasicoherentOn F .fppf :=
  sorry

end AlgebraicGeometry.GroupoidsOver
