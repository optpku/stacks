module

import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.FiniteType
import StacksCheckRecall

open SheafOfModules.RingedSite

universe u

/- Lemma 31.30.2: finite type of a quasi-coherent graded algebra on affine models implies
that its relative projective spectrum is of finite type and every integral twist is a finite
type module. -/
@[stacks 07ZY] #check
  (AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation.finiteType_and_twist_isFiniteType_of_finiteTypeAlgebra :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S}
      {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf} [𝒜.IsCommutative]
      {A σ : S.affineOpens → Type u}
      [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
      [∀ U, AddSubgroupClass (σ U) (A U)]
      {sectionGrading : ∀ U : S.affineOpens, ℕ → σ U}
      [∀ U, GradedRing (sectionGrading U)]
      {P : ∀ U : S.affineOpens,
        AlgebraicGeometry.ProjTwistPresentation (sectionGrading U)}
      {model : ∀ (U : S.affineOpens) (d : ℕ),
        (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+
          sectionGrading U d},
      (hModel : ∀ U : S.affineOpens,
        AlgebraicGeometry.AffineOpenSectionProj.IsAffineOpenSectionModel
          (sectionGrading U) 𝒜 U (model U)) →
      (presentation : AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation
        𝒜 A σ sectionGrading P (fun U d ↦ (model U d).toEquiv) p) →
      (hft : SheafOfModules.RingedSite.GradedAlgebraSheaf.FiniteTypeOnAffineModels
        (A := A) (σ := σ) 𝒜 sectionGrading (model := model) hModel) →
      AlgebraicGeometry.Scheme.Hom.FiniteType p ∧
        ∀ d : ℤ, (presentation.twistAlgebra d).IsFiniteType)
