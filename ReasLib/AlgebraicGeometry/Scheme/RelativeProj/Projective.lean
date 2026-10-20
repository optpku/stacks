/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Realization
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.RingTheory.GradedAlgebra.GeneratedBy

/-!
# Projectivity of relative projective spectra

This module relates affine-local generation of a graded algebra in degree one to projectivity
of the structural morphism of its equipped relative projective spectrum.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeProjRealization

/-- The structural morphism of an equipped relative projective spectrum is projective when its
affine graded models are generated in degree one and its degree-one sheaf is of finite type. -/
@[stacks 0B3U]
theorem projective_of_generatedByDegreeOne
    {S : Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf ℤ}
    [𝒜.IsCommutative]
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
      sectionRestrict sectionRestrict_spec)
    (hgenerated : ∀ U : S.affineOpens,
      GradedAlgebra.GeneratedBy (sectionGrading U) 1)
    (hfinite : (𝒜 (Int.ofNat 1)).IsFiniteType) :
    Projective (Scheme.relativeProjπ R) := sorry

end AlgebraicGeometry.Scheme.RelativeProjRealization

namespace AlgebraicGeometry.Scheme.Hom

variable {S X : Scheme.{u}} {p : X ⟶ S}

namespace AbsoluteProjModel

/-- The projective spectrum of an affine graded model is projective over its base when degree
zero is finite over the base and the total ring is finite type over degree zero. -/
theorem projective_toSpecBase (D : AbsoluteProjModel)
    (hfinite : D.baseToZero.hom.Finite)
    (hfiniteType : D.degreeZeroToRing.hom.FiniteType) :
    AlgebraicGeometry.Projective D.toSpecBase := sorry

end AbsoluteProjModel

namespace RelativeProjPresentation.FiniteDegreeZeroAlgebra

/-- A relative projective-spectrum morphism is locally projective when its degree-zero
algebras are finite over their bases and its total algebras are finite type over degree zero. -/
theorem locallyProjective {P : RelativeProjPresentation p}
    (hfinite : P.FiniteDegreeZeroAlgebra)
    (hfiniteType : P.FiniteTypeAsDegreeZeroAlgebra) :
    AlgebraicGeometry.LocallyProjective p := sorry

end RelativeProjPresentation.FiniteDegreeZeroAlgebra

end AlgebraicGeometry.Scheme.Hom
