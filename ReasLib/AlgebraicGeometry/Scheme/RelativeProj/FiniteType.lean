/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.TwistGluing

/-!
# Finite type relative projective spectra

This module records the affine-model finite type condition for a graded algebra sheaf and
its consequences for a relative projective spectrum and its integral twists.
-/

@[expose] public section

open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AffineOpenSectionProj

/-- The structure homomorphism from functions on an affine base open to the total ring of a
compatible graded section-ring model. -/
noncomputable def sectionRingStructureMap
    {S : Scheme.{u}} {A σ : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] {sectionGrading : ℕ → σ} [GradedRing sectionGrading]
    {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf} {U : S.affineOpens}
    {model : ∀ d : ℕ,
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading d}
    (hModel : IsAffineOpenSectionModel sectionGrading 𝒜 U model) :
    S.presheaf.obj (Opposite.op (U : S.Opens)) →+* A :=
  (algebraMap (sectionGrading 0) A).comp
    (degreeZeroStructureMap sectionGrading 𝒜 U model hModel)

end AlgebraicGeometry.AffineOpenSectionProj

namespace SheafOfModules.RingedSite.GradedAlgebraSheaf

/-- A graded algebra sheaf is of finite type on fixed affine models when it is
quasi-coherent and every affine base section ring maps finitely to the corresponding total
graded section ring. -/
def FiniteTypeOnAffineModels
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
        (hModel U)).FiniteType

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

/-- Finite type of the affine graded section-ring models makes the structural morphism of
their relative projective spectrum finite type. -/
theorem finiteType_of_finiteTypeAlgebra
    {model : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading U d}
    (hModel : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel
        (sectionGrading U) 𝒜 U (model U))
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P (fun U d ↦ (model U d).toEquiv) p)
    (hft : 𝒜.FiniteTypeOnAffineModels sectionGrading model hModel) :
    Scheme.Hom.FiniteType p := sorry

/-- Finite type of the affine graded section-ring models makes every integral twist on their
relative projective spectrum a finite type module. -/
theorem twist_isFiniteType_of_finiteTypeAlgebra
    {model : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading U d}
    (hModel : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel
        (sectionGrading U) 𝒜 U (model U))
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P (fun U d ↦ (model U d).toEquiv) p)
    (hft : 𝒜.FiniteTypeOnAffineModels sectionGrading model hModel)
    (d : ℤ) :
    (presentation.twistAlgebra d).IsFiniteType := sorry

/-- Finite type of the affine graded section-ring models makes the structural morphism of
their relative projective spectrum finite type and all its integral twists finite type. -/
theorem finiteType_and_twist_isFiniteType_of_finiteTypeAlgebra
    {model : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading U d}
    (hModel : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel
        (sectionGrading U) 𝒜 U (model U))
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P (fun U d ↦ (model U d).toEquiv) p)
    (hft : 𝒜.FiniteTypeOnAffineModels sectionGrading model hModel) :
    Scheme.Hom.FiniteType p ∧
      ∀ d : ℤ, (presentation.twistAlgebra d).IsFiniteType := sorry

end AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation

namespace AlgebraicGeometry.Scheme.Hom

variable {S X : Scheme.{u}} {p : X ⟶ S}

namespace AbsoluteProjModel

/-- The base-to-total-ring map of an affine projective-spectrum model factors through its
degree-zero subring. -/
theorem degreeZeroToRing_comp_baseToZero (D : AbsoluteProjModel) :
    D.degreeZeroToRing.hom.comp D.baseToZero.hom = D.baseToRing.hom := sorry

end AbsoluteProjModel

namespace RelativeProjPresentation

/-- A relative projective-spectrum presentation has finite degree-zero algebras when every
canonical base-to-degree-zero map is finite. -/
def FiniteDegreeZeroAlgebra (P : RelativeProjPresentation p) : Prop :=
  ∀ s : S, (P.affineChart s).affineAlgebra.baseToZero.hom.Finite

/-- A relative projective-spectrum presentation is affine-locally of finite type over the base
when every canonical base-to-total-ring map is of finite type. -/
def FiniteTypeAsBaseAlgebra (P : RelativeProjPresentation p) : Prop :=
  ∀ s : S, (P.affineChart s).affineAlgebra.baseToRing.hom.FiniteType

/-- If the degree-zero algebras are finite over their bases, finite type over degree zero is
equivalent to finite type over the base. -/
theorem finiteTypeConditions_iff (P : RelativeProjPresentation p) :
    (P.FiniteDegreeZeroAlgebra ∧ P.FiniteTypeAsDegreeZeroAlgebra) ↔
      (P.FiniteDegreeZeroAlgebra ∧ P.FiniteTypeAsBaseAlgebra) := sorry

end RelativeProjPresentation

end AlgebraicGeometry.Scheme.Hom
