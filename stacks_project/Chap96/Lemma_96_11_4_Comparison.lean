/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import stacks_project.Chap96.Lemma_96_8_1_RingedSite

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

/-- The projection of a category fibred in groupoids is continuous for the
inherited fppf topology. -/
instance inheritedFppfTopology_isContinuous (X : GroupoidsOver S) :
    X.p.IsContinuous (inheritedFppfTopology X) (Scheme.fppfTopology.over S) :=
  Functor.inheritedTopology.isContinuous X.p (Scheme.fppfTopology.over S)

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

/-- Ring-to-abelian-group sheaf composition exists on every slice of the
inherited fppf topology. -/
instance inheritedFppfTopology_over_hasSheafCompose (X : GroupoidsOver S) :
    ∀ x, ((inheritedFppfTopology X).over x).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  sorry

/-- Weak sheafification of abelian groups exists on every slice of the inherited
fppf topology. -/
instance inheritedFppfTopology_over_hasWeakSheafify (X : GroupoidsOver S) :
    ∀ x, HasWeakSheafify ((inheritedFppfTopology X).over x) AddCommGrpCat.{u} :=
  sorry

/-- Sheafification equivalences on slices of the inherited fppf topology are
exactly the locally bijective morphisms. -/
instance inheritedFppfTopology_over_wEqualsLocallyBijective
    (X : GroupoidsOver S) :
    ∀ x, ((inheritedFppfTopology X).over x).WEqualsLocallyBijective
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

/-- `F` is an object of `Mod(𝒳_τ, 𝒪_𝒳)` and is quasi-coherent there in the
sense of Modules on Sites, Definition 18.23.1. -/
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

/-- On the fppf associated site, `isQuasicoherentOn` recovers quasi-coherence of
Definition 96.11.1 on `(𝒳_fppf, 𝒪_𝒳)`. -/
theorem isQuasicoherentOn_fppf_iff_isQuasicoherent {X : GroupoidsOver S}
    (F : PresheafOfModules.{u} (structureSheaf X).obj) :
    isQuasicoherentOn F .fppf ↔
      ∃ h : Presheaf.IsSheaf (inheritedFppfTopology X) F.presheaf,
        (⟨F, h⟩ : SheafOfModules.{u} (structureSheaf X)).IsQuasicoherent :=
  sorry

end AlgebraicGeometry.GroupoidsOver
