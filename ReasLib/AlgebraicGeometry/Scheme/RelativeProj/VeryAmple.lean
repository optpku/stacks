/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.DegreeOneQuotient
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.DegreeOneTwists
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery

/-!
# Very ample twists on relative projective spectra

This file relates degree-one generation of the affine graded models in a relative
projective-spectrum realization to the projective-bundle presentation of its first twist.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation

/-- A morphism to the projective bundle of the degree-one piece is induced by the canonical
degree-one map when the pulled-back tautological quotient, with its source transported along
the lift triangle, is the adjoint of that map up to the displayed target isomorphism. -/
def IsInducedByDegreeOne
    {S : Scheme.{u}} {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf}
    {A σ : S.affineOpens → Type u}
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    {sectionGrading : ∀ U : S.affineOpens, ℕ → σ U}
    [∀ U, GradedRing (sectionGrading U)]
    {P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U)}
    {model : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃ sectionGrading U d}
    {X Q : Scheme.{u}} {p : X ⟶ S} {π : Q ⟶ S}
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model p)
    (hπ : ProjectiveBundle.Representation π (𝒜 (Int.ofNat 1)))
    (i : X ⟶ Q) : Prop :=
  ∃ (hi : i ≫ π = p)
      (e : presentation.twistAlgebra 1 ≅
        (Scheme.Modules.pullback i).obj (ProjectiveBundle.tautologicalSheaf π hπ)),
    ((ProjectiveBundle.Lift.pullbackSourceIso
        (⟨i, hi⟩ : ProjectiveBundle.Lift π p) (𝒜 (Int.ofNat 1))).inv ≫
      (Scheme.Modules.pullback i).map (ProjectiveBundle.tautologicalQuotient π hπ).hom) ≫
        e.inv =
      ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv
        (𝒜 (Int.ofNat 1)) (presentation.twistAlgebra 1)).symm
          (presentation.psi.hom 1)

/-- For an equipped relative projective spectrum generated in degree one, the first twist is
invertible and is the tautological pullback along the canonical closed immersion into the
projective bundle of the degree-one piece. -/
theorem twistOne_spec_of_generatedByDegreeOne
    {S : Scheme.{u}}
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
    (R : RelativeProjRealization 𝒜 hqc A σ sectionGrading model hModel P
      sectionRestrict sectionRestrict_spec)
    (presentation : RelativeProjTwist.Presentation 𝒜 A σ sectionGrading P
      (fun U d ↦ (model U d).toEquiv) R.toBase)
    (hlocal : ∀ U : S.affineOpens,
      presentation.localSchemeIso U = R.localIso U)
    (hgenerated : presentation.GeneratedByDegreeOne) :
    Scheme.Modules.Invertible (presentation.twistAlgebra 1) ∧
      ∃ (Q : Scheme.{u}) (π : Q ⟶ S)
        (hπ : ProjectiveBundle.Representation π (𝒜 (Int.ofNat 1)))
        (i : R.Y ⟶ Q),
        IsClosedImmersion i ∧
          presentation.IsInducedByDegreeOne hπ i ∧
            RelativelyVeryAmplePresentation R.toBase
              (presentation.twistAlgebra 1) π (𝒜 (Int.ofNat 1)) hπ i := sorry

/-- The first twist of an equipped degree-one-generated relative projective spectrum is
relatively very ample over its base. -/
theorem twistOne_relativelyVeryAmple_of_generatedByDegreeOne
    {S : Scheme.{u}}
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
    (R : RelativeProjRealization 𝒜 hqc A σ sectionGrading model hModel P
      sectionRestrict sectionRestrict_spec)
    (presentation : RelativeProjTwist.Presentation 𝒜 A σ sectionGrading P
      (fun U d ↦ (model U d).toEquiv) R.toBase)
    (hlocal : ∀ U : S.affineOpens,
      presentation.localSchemeIso U = R.localIso U)
    (hgenerated : presentation.GeneratedByDegreeOne) :
    RelativelyVeryAmple R.toBase (presentation.twistAlgebra 1) := sorry

end AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation
