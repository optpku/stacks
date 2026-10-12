/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.FinitePresentation
import StacksCheckRecall
import stacks_project.Chap31.Lemma_31_30_2

open SheafOfModules.RingedSite

universe u

/- Lemma 31.30.7: finite presentation of a quasi-coherent graded algebra on affine models implies
that its relative projective spectrum is of finite presentation and every integral twist is a
finite presentation module. -/
@[stacks 0D4D] #check
  (AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation.finitePresentation_and_twist_isFinitePresentation :
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
      (hfp : SheafOfModules.RingedSite.GradedAlgebraSheaf.FinitePresentationOnAffineModels
        (A := A) (σ := σ) 𝒜 sectionGrading (model := model) hModel) →
      AlgebraicGeometry.Scheme.Hom.FinitePresentation p ∧
        ∀ d : ℤ, (presentation.twistAlgebra d).IsFinitePresentation)
