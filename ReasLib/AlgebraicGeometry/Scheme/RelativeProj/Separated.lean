/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Realization

/-!
# Separatedness of relative projective spectra

The structural morphism of an equipped relative projective spectrum is separated.
-/

@[expose] public section

open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeProjRealization

/-- The structural morphism of an equipped relative projective spectrum is separated. -/
theorem isSeparated
    {S : Scheme.{u}}
    {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf} [𝒜.IsCommutative]
    {hqc : 𝒜.IsQuasicoherent}
    {A σ : S.affineOpens → Type u}
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    {sectionGrading : ∀ U : S.affineOpens, ℕ → σ U}
    [∀ U, GradedRing (sectionGrading U)]
    {model : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading U d}
    {hModel : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel
        (sectionGrading U) 𝒜 U (model U)}
    {P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U)}
    {sectionRestrict : ∀ ⦃U U' : S.affineOpens⦄,
      (U : S.Opens) ≤ (U' : S.Opens) → sectionGrading U' →+*ᵍ sectionGrading U}
    {sectionRestrict_spec :
      ∀ ⦃U U' : S.affineOpens⦄ (h : (U : S.Opens) ≤ (U' : S.Opens))
        (d : ℕ) (x : sectionGrading U' d),
        model U d
            ((((𝒜 (Int.ofNat d)).val.map (CategoryTheory.homOfLE h).op).hom)
              ((model U' d).symm x)) =
          (sectionRestrict h).gradedAddHom d x}
    (R : RelativeProjRealization 𝒜 hqc A σ sectionGrading model hModel P
      sectionRestrict sectionRestrict_spec) :
    IsSeparated (Scheme.relativeProjπ R) := sorry

end AlgebraicGeometry.Scheme.RelativeProjRealization
