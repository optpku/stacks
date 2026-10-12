/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.VeryAmple

open CategoryTheory
open AlgebraicGeometry
open SheafOfModules.RingedSite

universe u

/- Example 29.38.3: for a commutative quasi-coherent graded algebra with an equipped relative
projective-spectrum realization and compatible twist presentation, generation in degree one
makes the first twist invertible and identifies it with the tautological pullback along the
canonical closed immersion into the projective bundle of the degree-one piece. -/
@[stacks 07ZR] #check
  (AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation.twistOne_spec_of_generatedByDegreeOne :
    ∀ {S : Scheme.{u}}
      (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf) [𝒜.IsCommutative]
      (hqc : 𝒜.IsQuasicoherent)
      (A σ : S.affineOpens → Type u)
      [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
      [∀ U, AddSubgroupClass (σ U) (A U)]
      (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
      [∀ U, GradedRing (sectionGrading U)]
      (model : ∀ (U : S.affineOpens) (d : ℕ),
        (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading U d)
      (hModel : ∀ U : S.affineOpens,
        AffineOpenSectionProj.IsAffineOpenSectionModel
          (sectionGrading U) 𝒜 U (model U))
      (P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
      (sectionRestrict : ∀ ⦃U U' : S.affineOpens⦄,
        (U : S.Opens) ≤ (U' : S.Opens) → sectionGrading U' →+*ᵍ sectionGrading U)
      (sectionRestrict_spec :
        ∀ ⦃U U' : S.affineOpens⦄ (h : (U : S.Opens) ≤ (U' : S.Opens))
          (d : ℕ) (x : sectionGrading U' d),
          model U d
              ((((𝒜 (Int.ofNat d)).val.map (homOfLE h).op).hom)
                ((model U' d).symm x)) =
            (sectionRestrict h).gradedAddHom d x)
      (R : Scheme.RelativeProjRealization 𝒜 hqc A σ sectionGrading model hModel P
        sectionRestrict sectionRestrict_spec)
      (presentation : Scheme.RelativeProjTwist.Presentation 𝒜 A σ sectionGrading P
        (fun U d ↦ (model U d).toEquiv) R.toBase)
      (hlocal : ∀ U : S.affineOpens,
        presentation.localSchemeIso U = R.localIso U)
      (hgenerated : presentation.GeneratedByDegreeOne),
      Scheme.Modules.Invertible (presentation.twistAlgebra 1) ∧
        ∃ (Q : Scheme.{u}) (π : Q ⟶ S)
          (hπ : Scheme.ProjectiveBundle.Representation π (𝒜 (Int.ofNat 1)))
          (i : R.Y ⟶ Q),
          IsClosedImmersion i ∧
            presentation.IsInducedByDegreeOne hπ i ∧
              RelativelyVeryAmplePresentation R.toBase
                (presentation.twistAlgebra 1) π (𝒜 (Int.ofNat 1)) hπ i)

#check
  (AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation.twistOne_relativelyVeryAmple_of_generatedByDegreeOne :
    ∀ {S : Scheme.{u}}
      (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf) [𝒜.IsCommutative]
      (hqc : 𝒜.IsQuasicoherent)
      (A σ : S.affineOpens → Type u)
      [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
      [∀ U, AddSubgroupClass (σ U) (A U)]
      (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
      [∀ U, GradedRing (sectionGrading U)]
      (model : ∀ (U : S.affineOpens) (d : ℕ),
        (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading U d)
      (hModel : ∀ U : S.affineOpens,
        AffineOpenSectionProj.IsAffineOpenSectionModel
          (sectionGrading U) 𝒜 U (model U))
      (P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
      (sectionRestrict : ∀ ⦃U U' : S.affineOpens⦄,
        (U : S.Opens) ≤ (U' : S.Opens) → sectionGrading U' →+*ᵍ sectionGrading U)
      (sectionRestrict_spec :
        ∀ ⦃U U' : S.affineOpens⦄ (h : (U : S.Opens) ≤ (U' : S.Opens))
          (d : ℕ) (x : sectionGrading U' d),
          model U d
              ((((𝒜 (Int.ofNat d)).val.map (homOfLE h).op).hom)
                ((model U' d).symm x)) =
            (sectionRestrict h).gradedAddHom d x)
      (R : Scheme.RelativeProjRealization 𝒜 hqc A σ sectionGrading model hModel P
        sectionRestrict sectionRestrict_spec)
      (presentation : Scheme.RelativeProjTwist.Presentation 𝒜 A σ sectionGrading P
        (fun U d ↦ (model U d).toEquiv) R.toBase)
      (hlocal : ∀ U : S.affineOpens,
        presentation.localSchemeIso U = R.localIso U)
      (hgenerated : presentation.GeneratedByDegreeOne),
      RelativelyVeryAmple R.toBase (presentation.twistAlgebra 1))
