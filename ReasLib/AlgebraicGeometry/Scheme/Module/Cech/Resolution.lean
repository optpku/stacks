module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.HomologicalComplex
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Pushforward.Comparison
public import ReasLib.Topology.Presheaf.Cech.Coordinates

/-!
# Module-valued Čech resolutions on schemes

An indexed family of opens determines a functorial complex of module sheaves.  Its terms are
products of the restrictions to finite intersections, pushed forward to the ambient scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {ι : Type u}
variable [HasProducts X.Modules]

/-- The pushed-forward restriction belonging to one tuple of members of an open family. -/
abbrev openCoverModuleCechSummand
    (𝒰 : ι → X.Opens) (ℱ : X.Modules) (p : ℕ) :
    (Fin (p + 1) → ι) → X.Modules :=
  fun σ ↦
    (RingedSpace.modulePushforwardFromOpen
      (TopCat.Presheaf.Cech.intersection 𝒰 σ)).obj
        ((RingedSpace.moduleRestrictionToOpen X.toRingedSpace
          (TopCat.Presheaf.Cech.intersection 𝒰 σ)).obj ℱ)

/-- The product of pushed-forward restrictions over all tuples of a fixed length. -/
abbrev openCoverModuleCechTerm
    (𝒰 : ι → X.Opens) (ℱ : X.Modules) (p : ℕ) : X.Modules :=
  ∏ᶜ openCoverModuleCechSummand 𝒰 ℱ p

/-- Omitting an entry of a tuple induces the corresponding restriction morphism. -/
abbrev openCoverModuleCechRestriction
    (𝒰 : ι → X.Opens) (ℱ : X.Modules) {p : ℕ}
    (σ : Fin (p + 2) → ι) (j : Fin (p + 2)) :
    openCoverModuleCechSummand 𝒰 ℱ p (σ ∘ j.succAboveEmb) ⟶
      openCoverModuleCechSummand 𝒰 ℱ (p + 1) σ :=
  RingedSpace.OpenSubspace.Pushforward.restrictionMap
    (TopCat.Presheaf.Cech.intersection_le_succAbove 𝒰 σ j) ℱ

/-- The alternating Čech differential between consecutive product terms. -/
noncomputable def openCoverModuleCechDifferential
    (𝒰 : ι → X.Opens) (ℱ : X.Modules) (p : ℕ) :
    openCoverModuleCechTerm 𝒰 ℱ p ⟶ openCoverModuleCechTerm 𝒰 ℱ (p + 1) :=
  Pi.lift fun σ : Fin (p + 2) → ι ↦
    ∑ j : Fin (p + 2),
      (-1 : ℤ) ^ (j : ℕ) •
        (Pi.π (openCoverModuleCechSummand 𝒰 ℱ p) (σ ∘ j.succAboveEmb) ≫
          openCoverModuleCechRestriction 𝒰 ℱ σ j)

/-- Two consecutive alternating Čech differentials compose to zero. -/
theorem openCoverModuleCechDifferential_comp
    (𝒰 : ι → X.Opens) (ℱ : X.Modules) (p : ℕ) :
    openCoverModuleCechDifferential 𝒰 ℱ p ≫
      openCoverModuleCechDifferential 𝒰 ℱ (p + 1) = 0 := sorry

/-- The module-valued Čech complex of a module sheaf for an indexed open family. -/
noncomputable def openCoverModuleCechComplex
    (𝒰 : ι → X.Opens) (ℱ : X.Modules) : CochainComplex X.Modules ℕ :=
  CochainComplex.of
    (fun p ↦ openCoverModuleCechTerm 𝒰 ℱ p)
    (fun p ↦ openCoverModuleCechDifferential 𝒰 ℱ p)
    (openCoverModuleCechDifferential_comp 𝒰 ℱ)

/-- A module morphism induces a morphism on every pushed-forward restriction summand. -/
abbrev openCoverModuleCechSummandMap
    (𝒰 : ι → X.Opens) {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) (p : ℕ)
    (σ : Fin (p + 1) → ι) :
    openCoverModuleCechSummand 𝒰 ℱ p σ ⟶
      openCoverModuleCechSummand 𝒰 𝒢 p σ :=
  (RingedSpace.moduleRestrictionToOpen X.toRingedSpace
      (TopCat.Presheaf.Cech.intersection 𝒰 σ) ⋙
    RingedSpace.modulePushforwardFromOpen
      (TopCat.Presheaf.Cech.intersection 𝒰 σ)).map φ

/-- A module morphism induces a morphism between every pair of Čech terms. -/
noncomputable def openCoverModuleCechTermMap
    (𝒰 : ι → X.Opens) {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) (p : ℕ) :
    openCoverModuleCechTerm 𝒰 ℱ p ⟶ openCoverModuleCechTerm 𝒰 𝒢 p :=
  Limits.Pi.map fun σ ↦ openCoverModuleCechSummandMap 𝒰 φ p σ

/-- The degreewise maps induced by a module morphism commute with the Čech differential. -/
theorem openCoverModuleCechComplexMap_comm
    (𝒰 : ι → X.Opens) {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    ∀ p q, (ComplexShape.up ℕ).Rel p q →
      openCoverModuleCechTermMap 𝒰 φ p ≫ (openCoverModuleCechComplex 𝒰 𝒢).d p q =
        (openCoverModuleCechComplex 𝒰 ℱ).d p q ≫ openCoverModuleCechTermMap 𝒰 φ q := sorry

/-- A module morphism induces the corresponding morphism of Čech complexes. -/
noncomputable def openCoverModuleCechComplexMap
    (𝒰 : ι → X.Opens) {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    openCoverModuleCechComplex 𝒰 ℱ ⟶ openCoverModuleCechComplex 𝒰 𝒢 :=
  HomologicalComplex.Hom.mk
    (openCoverModuleCechTermMap 𝒰 φ)
    (openCoverModuleCechComplexMap_comm 𝒰 φ)

/-- The Čech complex map induced by an identity is the identity. -/
theorem openCoverModuleCechComplexMap_id
    (𝒰 : ι → X.Opens) (ℱ : X.Modules) :
    openCoverModuleCechComplexMap 𝒰 (𝟙 ℱ) = 𝟙 (openCoverModuleCechComplex 𝒰 ℱ) := sorry

/-- Čech complex maps preserve composition of module morphisms. -/
theorem openCoverModuleCechComplexMap_comp
    (𝒰 : ι → X.Opens) {ℱ 𝒢 ℋ : X.Modules} (φ : ℱ ⟶ 𝒢) (ψ : 𝒢 ⟶ ℋ) :
    openCoverModuleCechComplexMap 𝒰 (φ ≫ ψ) =
      openCoverModuleCechComplexMap 𝒰 φ ≫ openCoverModuleCechComplexMap 𝒰 ψ := sorry

/-- The functorial module-valued Čech resolution associated to a family of opens. -/
noncomputable def openCoverModuleCechComplexFunctor (𝒰 : ι → X.Opens) :
    X.Modules ⥤ CochainComplex X.Modules ℕ where
  obj ℱ := openCoverModuleCechComplex 𝒰 ℱ
  map φ := openCoverModuleCechComplexMap 𝒰 φ
  map_id ℱ := openCoverModuleCechComplexMap_id 𝒰 ℱ
  map_comp φ ψ := openCoverModuleCechComplexMap_comp 𝒰 φ ψ

/-- Evaluating the Čech-resolution functor gives the complex with product terms and alternating
differential. -/
@[simp]
theorem openCoverModuleCechComplexFunctor_obj
    (𝒰 : ι → X.Opens) (ℱ : X.Modules) :
    (openCoverModuleCechComplexFunctor 𝒰).obj ℱ = openCoverModuleCechComplex 𝒰 ℱ :=
  rfl

/-- The degree-zero map from a module to the product of its pushed-forward restrictions. -/
noncomputable def openCoverModuleCechAugmentationMap
    (𝒰 : ι → X.Opens) (ℱ : X.Modules) :
    ℱ ⟶ openCoverModuleCechTerm 𝒰 ℱ 0 :=
  Pi.lift fun σ : Fin 1 → ι ↦
    (RingedSpace.OpenSubspace.Pushforward.adjunction X.toRingedSpace
      (TopCat.Presheaf.Cech.intersection 𝒰 σ)).unit.app ℱ

/-- The degree-zero augmentation is killed by the first Čech differential. -/
theorem openCoverModuleCechAugmentation_comp_d_zero_one
    (𝒰 : ι → X.Opens) (ℱ : X.Modules) :
    openCoverModuleCechAugmentationMap 𝒰 ℱ ≫
      openCoverModuleCechDifferential 𝒰 ℱ 0 = 0 := sorry

/-- The augmentation morphism from a module in degree zero to its Čech complex. -/
noncomputable def openCoverModuleCechAugmentationApp
    (𝒰 : ι → X.Opens) (ℱ : X.Modules) :
    (CochainComplex.single₀ X.Modules).obj ℱ ⟶
      openCoverModuleCechComplex 𝒰 ℱ :=
  (CochainComplex.fromSingle₀Equiv (openCoverModuleCechComplex 𝒰 ℱ) ℱ).symm
    ⟨openCoverModuleCechAugmentationMap 𝒰 ℱ,
      openCoverModuleCechAugmentation_comp_d_zero_one 𝒰 ℱ⟩

/-- The Čech augmentation is natural in the module. -/
theorem openCoverModuleCechAugmentation_naturality
    (𝒰 : ι → X.Opens) {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    (CochainComplex.single₀ X.Modules).map φ ≫
        openCoverModuleCechAugmentationApp 𝒰 𝒢 =
      openCoverModuleCechAugmentationApp 𝒰 ℱ ≫
        (openCoverModuleCechComplexFunctor 𝒰).map φ := sorry

/-- The canonical natural augmentation from modules in degree zero to their Čech resolutions. -/
noncomputable def openCoverModuleCechAugmentation (𝒰 : ι → X.Opens) :
    CochainComplex.single₀ X.Modules ⟶ openCoverModuleCechComplexFunctor 𝒰 where
  app ℱ := openCoverModuleCechAugmentationApp 𝒰 ℱ
  naturality _ _ φ := openCoverModuleCechAugmentation_naturality 𝒰 φ

/-- For an open cover, the canonical augmentation to the module-valued Čech resolution is a
quasi-isomorphism. -/
theorem openCoverModuleCechAugmentation_quasiIso_of_isOpenCover
    (𝒰 : ι → X.Opens) (h𝒰 : IsOpenCover 𝒰) (ℱ : X.Modules) :
    QuasiIso ((openCoverModuleCechAugmentation 𝒰).app ℱ) := sorry

end AlgebraicGeometry.Scheme
