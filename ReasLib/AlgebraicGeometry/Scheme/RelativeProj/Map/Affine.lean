/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.Twist
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Map.Basic

/-!
# Affine restrictions of maps between relative projective spectra

This file records the restriction of a relative projective-spectrum map over an affine open of
the base and the comparison with the corresponding map of absolute projective spectra.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom.AbsoluteProjModel

/-- The subtype of elements in degree `d` of an explicit graded-ring model. -/
def homogeneousPiece (D : AbsoluteProjModel) (d : ℕ) : Type u :=
  { x : D.ring //
    x ∈ @SetLike.coe D.grade D.ring D.gradeSetLike (D.grading d) }

/-- The type of graded ring homomorphisms between two explicit graded-ring models. -/
abbrev GradedHom (D E : AbsoluteProjModel) :=
  @GradedRingHom ℕ D.ring E.ring D.grade E.grade inferInstance inferInstance
    D.gradeSetLike E.gradeSetLike D.grading E.grading

/-- The type of chosen integral-twist presentations attached to an explicit graded-ring model. -/
abbrev TwistPresentation (D : AbsoluteProjModel) :=
  @ProjTwistPresentation D.ring D.grade inferInstance D.gradeSetLike
    D.gradeAddSubgroupClass D.grading D.grading_inst

namespace GradedHom

/-- The degreewise additive homomorphism underlying a graded homomorphism of explicit models. -/
abbrev gradedAddHom {D E : AbsoluteProjModel} (ψ : D.GradedHom E) (d : ℕ) :=
  @GradedRingHom.gradedAddHom ℕ D.ring E.ring D.grade E.grade inferInstance inferInstance
    D.gradeSetLike E.gradeSetLike D.grading E.grading
    D.gradeAddSubgroupClass.toAddSubmonoidClass
    E.gradeAddSubgroupClass.toAddSubmonoidClass ψ d

/-- The natural open domain of the absolute projective-spectrum map induced by a graded
homomorphism of explicit models. -/
abbrev domain {D E : AbsoluteProjModel} (ψ : D.GradedHom E) :=
  @projMapDomain D.ring E.ring D.grade E.grade
    inferInstance D.gradeSetLike D.gradeAddSubgroupClass
    inferInstance E.gradeSetLike E.gradeAddSubgroupClass
    D.grading E.grading D.grading_inst E.grading_inst ψ

/-- A twist-compatible absolute projective-spectrum map attached to a graded homomorphism of
explicit models and chosen twist presentations. -/
abbrev ProjMap {D E : AbsoluteProjModel} (ψ : D.GradedHom E)
    (PD : D.TwistPresentation) (PE : E.TwistPresentation) :=
  @AlgebraicGeometry.ProjMap D.ring E.ring D.grade E.grade
    inferInstance D.gradeSetLike D.gradeAddSubgroupClass
    inferInstance E.gradeSetLike E.gradeAddSubgroupClass
    D.grading E.grading D.grading_inst E.grading_inst PD PE ψ

namespace ProjMap

/-- The scheme morphism underlying a twist-compatible map between explicit absolute models. -/
abbrev map {D E : AbsoluteProjModel} {ψ : D.GradedHom E}
    {PD : D.TwistPresentation} {PE : E.TwistPresentation} (f : ψ.ProjMap PD PE) :=
  @AlgebraicGeometry.ProjMap.map D.ring E.ring D.grade E.grade
    inferInstance D.gradeSetLike D.gradeAddSubgroupClass
    inferInstance E.gradeSetLike E.gradeAddSubgroupClass
    D.grading E.grading D.grading_inst E.grading_inst PD PE ψ f

/-- The degreewise twist comparison underlying a twist-compatible map between explicit absolute
models. -/
abbrev theta {D E : AbsoluteProjModel} {ψ : D.GradedHom E}
    {PD : D.TwistPresentation} {PE : E.TwistPresentation} (f : ψ.ProjMap PD PE) (n : ℤ) :=
  @AlgebraicGeometry.ProjMap.theta D.ring E.ring D.grade E.grade
    inferInstance D.gradeSetLike D.gradeAddSubgroupClass
    inferInstance E.gradeSetLike E.gradeAddSubgroupClass
    D.grading E.grading D.grading_inst E.grading_inst PD PE ψ f n

end ProjMap

end GradedHom

namespace TwistPresentation

/-- The degreewise actual twist carried by a presentation for an explicit absolute model. -/
abbrev actualTwist {D : AbsoluteProjModel} (P : D.TwistPresentation) (n : ℤ) :=
  @ProjTwistPresentation.actualTwist D.ring D.grade inferInstance D.gradeSetLike
    D.gradeAddSubgroupClass D.grading D.grading_inst P n

end TwistPresentation

end Scheme.Hom.AbsoluteProjModel

section

variable {S X Y : Scheme.{u}}
variable {pX : X ⟶ S} {pY : Y ⟶ S}
variable (P𝒜 : Scheme.Hom.RelativeProjPresentation pX)
variable (Pℬ : Scheme.Hom.RelativeProjPresentation pY)
variable (φ : P𝒜.algebra ⟶ Pℬ.algebra)

namespace RelativeProjMap

/-- The inverse image in the domain of a relative projective-spectrum map of the restriction of
its target over an affine open of the base. -/
abbrev affineRestrictionPreimage
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (W : S.affineOpens) : rφ.domain.toScheme.Opens :=
  rφ.map ⁻¹ᵁ (pX ⁻¹ᵁ (W : S.Opens))

/-- The open of the source scheme obtained by restricting the domain of a relative
projective-spectrum map over an affine open of the base. -/
abbrev affineRestrictionDomain
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (W : S.affineOpens) : Y.Opens :=
  rφ.domain.ι ''ᵁ (affineRestrictionPreimage P𝒜 Pℬ φ rφ W)

/-- The restriction of a relative projective-spectrum map over an affine open of the base. -/
abbrev affineRestrictionMap
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (W : S.affineOpens) :
    (affineRestrictionDomain P𝒜 Pℬ φ rφ W).toScheme ⟶
      (pX ⁻¹ᵁ (W : S.Opens)).toScheme :=
  ((rφ.domain.ι).isoImage (affineRestrictionPreimage P𝒜 Pℬ φ rφ W)).inv ≫
    Scheme.Hom.resLE rφ.map (pX ⁻¹ᵁ (W : S.Opens))
      (affineRestrictionPreimage P𝒜 Pℬ φ rφ W) le_rfl

/-- The source module of the degreewise comparison map restricted over an affine open of the
base. -/
abbrev affineRestrictionThetaSource
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (W : S.affineOpens) (n : ℤ) :
    (affineRestrictionDomain P𝒜 Pℬ φ rφ W).toScheme.Modules :=
  let V := affineRestrictionPreimage P𝒜 Pℬ φ rφ W
  let i : (affineRestrictionDomain P𝒜 Pℬ φ rφ W).toScheme ⟶ V.toScheme :=
    ((rφ.domain.ι).isoImage V).inv
  (Scheme.Modules.pullback i).obj
    ((Scheme.Modules.pullback V.ι).obj ((Scheme.Modules.pullback rφ.map).obj (P𝒜.twist n)))

/-- The target module of the degreewise comparison map restricted over an affine open of the
base. -/
abbrev affineRestrictionThetaTarget
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (W : S.affineOpens) (n : ℤ) :
    (affineRestrictionDomain P𝒜 Pℬ φ rφ W).toScheme.Modules :=
  let V := affineRestrictionPreimage P𝒜 Pℬ φ rφ W
  let i : (affineRestrictionDomain P𝒜 Pℬ φ rφ W).toScheme ⟶ V.toScheme :=
    ((rφ.domain.ι).isoImage V).inv
  (Scheme.Modules.pullback i).obj
    ((Scheme.Modules.pullback V.ι).obj ((Pℬ.twist n).restrict rφ.domain.ι))

/-- The degreewise comparison morphism restricted over an affine open of the base. -/
abbrev affineRestrictionTheta
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (W : S.affineOpens) (n : ℤ) :
    affineRestrictionThetaSource P𝒜 Pℬ φ rφ W n ⟶
      affineRestrictionThetaTarget P𝒜 Pℬ φ rφ W n :=
  let V := affineRestrictionPreimage P𝒜 Pℬ φ rφ W
  let i : (affineRestrictionDomain P𝒜 Pℬ φ rφ W).toScheme ⟶ V.toScheme :=
    ((rφ.domain.ι).isoImage V).inv
  (Scheme.Modules.pullback i).map ((Scheme.Modules.pullback V.ι).map (rφ.theta n))

/-- An affine-chart comparison between a relative projective-spectrum map and the absolute
projective-spectrum map induced on sections over an affine base open. -/
structure AffineChartCompatibility
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (W : S.affineOpens) where
  /-- The explicit graded-ring model for the target of the restricted map. -/
  projModelX : Scheme.Hom.AbsoluteProjModel
  /-- The explicit graded-ring model for the source of the restricted map. -/
  projModelY : Scheme.Hom.AbsoluteProjModel
  /-- A chosen integral-twist presentation on the target affine model. -/
  projPresentationX : projModelX.TwistPresentation
  /-- A chosen integral-twist presentation on the source affine model. -/
  projPresentationY : projModelY.TwistPresentation
  /-- The affine base is identified with the degree-zero spectrum of the target model. -/
  specZeroIsoX : (W : S.Opens).toScheme ≅ projModelX.specZero
  /-- The affine base is identified with the degree-zero spectrum of the source model. -/
  specZeroIsoY : (W : S.Opens).toScheme ≅ projModelY.specZero
  /-- The degree-`d` sections of the target presentation agree with the degree-`d` part of its
  affine model. -/
  degreePieceSectionsIsoX :
    ∀ d : ℕ,
      (P𝒜.algebra (Int.ofNat d)).val.obj (Opposite.op (W : S.Opens)) ≃
        projModelX.homogeneousPiece d
  /-- The degree-`d` sections of the source presentation agree with the degree-`d` part of its
  affine model. -/
  degreePieceSectionsIsoY :
    ∀ d : ℕ,
      (Pℬ.algebra (Int.ofNat d)).val.obj (Opposite.op (W : S.Opens)) ≃
        projModelY.homogeneousPiece d
  /-- The graded ring homomorphism on sections over the affine base open. -/
  sectionMap : projModelX.GradedHom projModelY
  /-- The graded ring homomorphism is induced degreewise by the algebra-sheaf morphism. -/
  sectionMap_spec :
    ∀ d : ℕ, ∀ x : projModelX.homogeneousPiece d,
      degreePieceSectionsIsoY d
          ((((φ.hom (Int.ofNat d)).val.app (Opposite.op (W : S.Opens))).hom)
            ((degreePieceSectionsIsoX d).symm x)) =
        (sectionMap.gradedAddHom d) x
  /-- The absolute projective spectrum of the target model is the target affine restriction. -/
  projIsoX : projModelX.proj ≅ (pX ⁻¹ᵁ (W : S.Opens)).toScheme
  /-- The absolute projective spectrum of the source model is the source affine restriction. -/
  projIsoY : projModelY.proj ≅ (pY ⁻¹ᵁ (W : S.Opens)).toScheme
  /-- The target affine model is compatible with the structural morphism to the base. -/
  projIsoX_over_base :
    projIsoX.inv ≫ projModelX.toSpecZero =
      (pX ∣_ (W : S.Opens)) ≫ specZeroIsoX.hom
  /-- The source affine model is compatible with the structural morphism to the base. -/
  projIsoY_over_base :
    projIsoY.inv ≫ projModelY.toSpecZero =
      (pY ∣_ (W : S.Opens)) ≫ specZeroIsoY.hom
  /-- The absolute projective-spectrum map induced by the homomorphism on sections. -/
  localProjMap : sectionMap.ProjMap projPresentationX projPresentationY
  /-- The natural domain of the absolute map is identified with the affine restriction of the
  relative domain. -/
  domainIso :
    sectionMap.domain.toScheme ≅
      (affineRestrictionDomain P𝒜 Pℬ φ rφ W).toScheme
  /-- The domain identification is compatible with the inclusions into the source scheme. -/
  domain_over_source :
    domainIso.hom ≫ (affineRestrictionDomain P𝒜 Pℬ φ rφ W).ι =
      sectionMap.domain.ι ≫ projIsoY.hom ≫ (pY ⁻¹ᵁ (W : S.Opens)).ι
  /-- The restricted relative map agrees with the absolute projective-spectrum map. -/
  map_eq :
    domainIso.hom ≫ affineRestrictionMap P𝒜 Pℬ φ rφ W =
      localProjMap.map ≫ projIsoX.hom
  /-- The source of the absolute twist comparison is identified with the pullback of the
  restricted relative source twist. -/
  thetaSourceIso :
    ∀ n : ℤ,
      (Scheme.Modules.pullback localProjMap.map).obj (projPresentationX.actualTwist n) ≅
        (Scheme.Modules.pullback domainIso.hom).obj
          (affineRestrictionThetaSource P𝒜 Pℬ φ rφ W n)
  /-- The target of the absolute twist comparison is identified with the pullback of the
  restricted relative target twist. -/
  thetaTargetIso :
    ∀ n : ℤ,
      (Scheme.Modules.pullback sectionMap.domain.ι).obj (projPresentationY.actualTwist n) ≅
        (Scheme.Modules.pullback domainIso.hom).obj
          (affineRestrictionThetaTarget P𝒜 Pℬ φ rφ W n)
  /-- The restricted degreewise comparison agrees with the absolute twist comparison after
  transport through the chosen identifications. -/
  theta_eq :
    ∀ n : ℤ,
      localProjMap.theta n ≫ (thetaTargetIso n).hom =
        (thetaSourceIso n).hom ≫
          (Scheme.Modules.pullback domainIso.hom).map
            (affineRestrictionTheta P𝒜 Pℬ φ rφ W n)

namespace AffineChartCompatibility

/-- Transport an affine-chart comparison along an equality of relative projective-spectrum
maps. -/
def ofEq
    {rφ rφ' : RelativeProjMap P𝒜 Pℬ φ}
    {W : S.affineOpens}
    (h : rφ = rφ')
    (C : AffineChartCompatibility P𝒜 Pℬ φ rφ W) :
    AffineChartCompatibility P𝒜 Pℬ φ rφ' W :=
  h ▸ C

/-- An affine-chart comparison simultaneously satisfies its section-map, base, domain, scheme-map,
and degreewise twist compatibility laws. -/
theorem spec
    {rφ : RelativeProjMap P𝒜 Pℬ φ}
    {W : S.affineOpens}
    (C : AffineChartCompatibility P𝒜 Pℬ φ rφ W) :
    (∀ d : ℕ, ∀ x : C.projModelX.homogeneousPiece d,
      C.degreePieceSectionsIsoY d
          ((((φ.hom (Int.ofNat d)).val.app (Opposite.op (W : S.Opens))).hom)
            ((C.degreePieceSectionsIsoX d).symm x)) =
        (C.sectionMap.gradedAddHom d) x) ∧
      (C.projIsoX.inv ≫ C.projModelX.toSpecZero =
        (pX ∣_ (W : S.Opens)) ≫ C.specZeroIsoX.hom) ∧
      (C.projIsoY.inv ≫ C.projModelY.toSpecZero =
        (pY ∣_ (W : S.Opens)) ≫ C.specZeroIsoY.hom) ∧
      (C.domainIso.hom ≫ (affineRestrictionDomain P𝒜 Pℬ φ rφ W).ι =
        C.sectionMap.domain.ι ≫ C.projIsoY.hom ≫ (pY ⁻¹ᵁ (W : S.Opens)).ι) ∧
      (C.domainIso.hom ≫ affineRestrictionMap P𝒜 Pℬ φ rφ W =
        C.localProjMap.map ≫ C.projIsoX.hom) ∧
      (∀ n : ℤ,
        C.localProjMap.theta n ≫ (C.thetaTargetIso n).hom =
          (C.thetaSourceIso n).hom ≫
            (Scheme.Modules.pullback C.domainIso.hom).map
              (affineRestrictionTheta P𝒜 Pℬ φ rφ W n)) := sorry

end AffineChartCompatibility

/-- There is a unique relative projective-spectrum map whose restriction over every affine base
open agrees with the absolute projective-spectrum map induced on sections. -/
theorem existsUnique_of_affine :
    ∃! rφ : RelativeProjMap P𝒜 Pℬ φ,
      ∀ W : S.affineOpens, Nonempty (AffineChartCompatibility P𝒜 Pℬ φ rφ W) := sorry

/-- Two relative projective-spectrum maps that agree with the induced absolute map over every
affine base open are equal. -/
theorem eq_of_affine
    {rφ rφ' : RelativeProjMap P𝒜 Pℬ φ}
    (hcompat : ∀ W : S.affineOpens, Nonempty (AffineChartCompatibility P𝒜 Pℬ φ rφ W))
    (hcompat' : ∀ W : S.affineOpens, Nonempty (AffineChartCompatibility P𝒜 Pℬ φ rφ' W)) :
    rφ = rφ' := sorry

/-- The restriction of a relative projective-spectrum map over an affine base open commutes with
the structural morphisms to that open. -/
theorem affineRestrictionMap_over_base
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (W : S.affineOpens) :
    affineRestrictionMap P𝒜 Pℬ φ rφ W ≫
        (pX ∣_ (W : S.Opens)) ≫ (W : S.Opens).ι =
      (affineRestrictionDomain P𝒜 Pℬ φ rφ W).ι ≫ pY := sorry

end RelativeProjMap

end

end AlgebraicGeometry
