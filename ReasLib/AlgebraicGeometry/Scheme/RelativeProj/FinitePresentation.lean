/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.FiniteType

/-!
# Finite presentation of relative projective spectra

This module records the affine-model finite-presentation condition for a graded algebra sheaf and
its consequences for a relative projective spectrum and its integral twists.
-/

@[expose] public section

open SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite.GradedAlgebraSheaf

/-- A graded algebra sheaf is of finite presentation on fixed affine models when it is
quasi-coherent and every affine base section ring maps finitely presentedly to the corresponding
total graded section ring. -/
def FinitePresentationOnAffineModels
    {S : AlgebraicGeometry.Scheme.{u}} (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf)
    {A σ : S.affineOpens → Type u}
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
    [∀ U, GradedRing (sectionGrading U)]
    (model : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading U d)
    (hModel : ∀ U : S.affineOpens,
      AlgebraicGeometry.AffineOpenSectionProj.IsAffineOpenSectionModel
        (sectionGrading U) 𝒜 U (model U)) : Prop :=
  𝒜.IsQuasicoherent ∧
    ∀ U : S.affineOpens,
      (AlgebraicGeometry.AffineOpenSectionProj.sectionRingStructureMap
        (hModel U)).FinitePresentation

namespace FinitePresentationOnAffineModels

/-- Finite presentation of all affine graded section-ring models implies finite type on the same
models. -/
theorem finiteType
    {S : AlgebraicGeometry.Scheme.{u}} {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf}
    {A σ : S.affineOpens → Type u}
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    {sectionGrading : ∀ U : S.affineOpens, ℕ → σ U}
    [∀ U, GradedRing (sectionGrading U)]
    {model : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading U d}
    {hModel : ∀ U : S.affineOpens,
      AlgebraicGeometry.AffineOpenSectionProj.IsAffineOpenSectionModel
        (sectionGrading U) 𝒜 U (model U)}
    (hfp : 𝒜.FinitePresentationOnAffineModels sectionGrading model hModel) :
    𝒜.FiniteTypeOnAffineModels sectionGrading model hModel := sorry

end FinitePresentationOnAffineModels

end SheafOfModules.RingedSite.GradedAlgebraSheaf

namespace AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation

variable {S X : Scheme.{u}} {p : X ⟶ S}
variable {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf} [𝒜.IsCommutative]
variable {A σ : S.affineOpens → Type u}
variable [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
variable [∀ U, AddSubgroupClass (σ U) (A U)]
variable {sectionGrading : ∀ U : S.affineOpens, ℕ → σ U}
variable [∀ U, GradedRing (sectionGrading U)]
variable {P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U)}

/-- Finite presentation of the affine graded section-ring models makes the structural morphism of
their relative projective spectrum finitely presented. -/
theorem finitePresentation_of_finitePresentationAlgebra
    {model : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading U d}
    (hModel : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel
        (sectionGrading U) 𝒜 U (model U))
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P (fun U d ↦ (model U d).toEquiv) p)
    (hfp : 𝒜.FinitePresentationOnAffineModels sectionGrading model hModel) :
    Scheme.Hom.FinitePresentation p := sorry

/-- Finite presentation of the affine graded section-ring models makes every integral twist on
their relative projective spectrum a finitely presented module. -/
theorem twist_isFinitePresentation_of_finitePresentationAlgebra
    {model : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading U d}
    (hModel : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel
        (sectionGrading U) 𝒜 U (model U))
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P (fun U d ↦ (model U d).toEquiv) p)
    (hfp : 𝒜.FinitePresentationOnAffineModels sectionGrading model hModel)
    (d : ℤ) :
    (presentation.twistAlgebra d).IsFinitePresentation := sorry

/-- Finite presentation of the affine graded section-ring models makes the structural morphism of
their relative projective spectrum finitely presented and all integral twists finitely presented
modules. -/
theorem finitePresentation_and_twist_isFinitePresentation
    {model : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading U d}
    (hModel : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel
        (sectionGrading U) 𝒜 U (model U))
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P (fun U d ↦ (model U d).toEquiv) p)
    (hfp : 𝒜.FinitePresentationOnAffineModels sectionGrading model hModel) :
    Scheme.Hom.FinitePresentation p ∧
      ∀ d : ℤ, (presentation.twistAlgebra d).IsFinitePresentation := sorry

end AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation
