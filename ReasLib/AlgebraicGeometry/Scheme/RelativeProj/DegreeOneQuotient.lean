/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.DegreeOneTwists
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.GeneratedByDegreeOne
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Presentation
public import ReasLib.CategoryTheory.Monoidal.InvertibleQuotient

/-!
# Degree-one quotients of relative projective spectra

An explicit twist presentation of a relative projective spectrum provides a
canonical adjoint map from the pulled-back degree-one piece to the first twist.
Under degree-one generation this is an invertible quotient.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation

/-- Thin presentation shorthand for `GradedAlgebra.GeneratedBy` on every affine model.

This is generation over degree zero, as used for invertible twists and in Stacks, Tag 07ZR.
It does not require the structure sheaf to surject onto degree zero. The intrinsic property
over the structure sheaf is owned by `GradedAlgebraSheaf.GeneratedByDegreeOne`; the bridge
`generatedByDegreeOne_intrinsic` records the additional hypotheses. -/
abbrev GeneratedByDegreeOne
    {S : Scheme.{u}} {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf}
    {A σ : S.affineOpens → Type u}
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    {sectionGrading : ∀ U : S.affineOpens, ℕ → σ U}
    [∀ U, GradedRing (sectionGrading U)]
    {P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U)}
    {model : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃ sectionGrading U d}
    {X : Scheme.{u}} {p : X ⟶ S}
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model p) : Prop :=
  ∀ U : S.affineOpens, GradedAlgebra.GeneratedBy (sectionGrading U) 1

/-- Generation in the chosen affine models implies intrinsic generation over the structure
sheaf when the additive models preserve unit and multiplication and their degree-zero structure
maps are surjective. Bare degreewise equivalences in a twist presentation do not supply these
compatibilities. -/
theorem generatedByDegreeOne_intrinsic
    {S : Scheme.{u}} {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf}
    {A σ : S.affineOpens → Type u}
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    {sectionGrading : ∀ U : S.affineOpens, ℕ → σ U}
    [∀ U, GradedRing (sectionGrading U)]
    {P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U)}
    (model : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading U d)
    (hModel : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel (sectionGrading U) 𝒜 U (model U))
    {X : Scheme.{u}} {p : X ⟶ S}
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P (fun U d ↦ (model U d).toEquiv) p)
    (hgenerated : presentation.GeneratedByDegreeOne)
    (hzero : ∀ U : S.affineOpens,
      Function.Surjective
        (AffineOpenSectionProj.degreeZeroStructureMap
          (sectionGrading U) 𝒜 U (model U) (hModel U))) :
    GradedAlgebraSheaf.GeneratedByDegreeOne 𝒜 :=
  GradedAlgebraSheaf.generatedByDegreeOne_of_affineOpenSectionModels
    𝒜 A σ sectionGrading model hModel hzero hgenerated

end AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation

namespace AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation

variable {S X : Scheme.{u}} {p : X ⟶ S}

/-- Raw affine and twist data presenting the first twist of a relative projective spectrum. -/
structure DegreeOneTwist (P : RelativeProjPresentation p) where
  /-- The affine coefficient rings used by the twist presentation. -/
  affineRing : S.affineOpens → Type u
  /-- The types of homogeneous components in the affine coefficient rings. -/
  homogeneousCarrier : S.affineOpens → Type u
  /-- The commutative ring structures on the affine coefficient rings. -/
  affineRingComm : ∀ U, CommRing (affineRing U)
  /-- The homogeneous components are represented as subsets. -/
  homogeneousCarrierSetLike : ∀ U, SetLike (homogeneousCarrier U) (affineRing U)
  /-- The homogeneous components are additive subgroups. -/
  homogeneousCarrierAddSubgroup :
    ∀ U, AddSubgroupClass (homogeneousCarrier U) (affineRing U)
  /-- The nonnegative affine gradings. -/
  sectionGrading : ∀ U : S.affineOpens, ℕ → homogeneousCarrier U
  /-- The affine gradings are graded-ring decompositions. -/
  sectionGradingRing :
    -- Local instance justification (defeq pin): expose the stored affine ring structures.
    letI ring : ∀ U, CommRing (affineRing U) := affineRingComm
    -- Local instance justification (defeq pin): expose the stored homogeneous carriers.
    letI setLike : ∀ U, SetLike (homogeneousCarrier U) (affineRing U) :=
      homogeneousCarrierSetLike
    -- Local instance justification (defeq pin): expose the stored additive subgroup structures.
    letI addSubgroup : ∀ U, AddSubgroupClass (homogeneousCarrier U) (affineRing U) :=
      homogeneousCarrierAddSubgroup
    ∀ U, GradedRing (sectionGrading U)
  /-- Absolute projective-twist presentations on the affine charts. -/
  absoluteTwist :
    -- Local instance justification (defeq pin): expose the stored affine ring structures.
    letI ring : ∀ U, CommRing (affineRing U) := affineRingComm
    -- Local instance justification (defeq pin): expose the stored homogeneous carriers.
    letI setLike : ∀ U, SetLike (homogeneousCarrier U) (affineRing U) :=
      homogeneousCarrierSetLike
    -- Local instance justification (defeq pin): expose the stored additive subgroup structures.
    letI addSubgroup : ∀ U, AddSubgroupClass (homogeneousCarrier U) (affineRing U) :=
      homogeneousCarrierAddSubgroup
    -- Local instance justification (defeq pin): expose the stored graded-ring structures.
    letI grading : ∀ U, GradedRing (sectionGrading U) := sectionGradingRing
    ∀ U, ProjTwistPresentation (sectionGrading U)
  /-- The degreewise comparison with sections of the relative graded algebra. -/
  sectionModel :
    -- Local instance justification (defeq pin): expose the stored affine ring structures.
    letI ring : ∀ U, CommRing (affineRing U) := affineRingComm
    -- Local instance justification (defeq pin): expose the stored homogeneous carriers.
    letI setLike : ∀ U, SetLike (homogeneousCarrier U) (affineRing U) :=
      homogeneousCarrierSetLike
    ∀ (U : S.affineOpens) (d : ℕ),
      (P.algebra (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃
        sectionGrading U d
  /-- The raw relative twist presentation against the relative-Proj algebra. -/
  twistPresentation :
    -- Local instance justification (defeq pin): expose the stored affine ring structures.
    letI ring : ∀ U, CommRing (affineRing U) := affineRingComm
    -- Local instance justification (defeq pin): expose the stored homogeneous carriers.
    letI setLike : ∀ U, SetLike (homogeneousCarrier U) (affineRing U) :=
      homogeneousCarrierSetLike
    -- Local instance justification (defeq pin): expose the stored additive subgroup structures.
    letI addSubgroup : ∀ U, AddSubgroupClass (homogeneousCarrier U) (affineRing U) :=
      homogeneousCarrierAddSubgroup
    -- Local instance justification (defeq pin): expose the stored graded-ring structures.
    letI grading : ∀ U, GradedRing (sectionGrading U) := sectionGradingRing
    RelativeProjTwist.Presentation P.algebra affineRing homogeneousCarrier
      sectionGrading absoluteTwist sectionModel p
  /-- Every affine model is generated over degree zero by its degree-one component. -/
  generatedByDegreeOne :
    -- Local instance justification (defeq pin): expose the stored affine ring structures.
    letI ring : ∀ U, CommRing (affineRing U) := affineRingComm
    -- Local instance justification (defeq pin): expose the stored homogeneous carriers.
    letI setLike : ∀ U, SetLike (homogeneousCarrier U) (affineRing U) :=
      homogeneousCarrierSetLike
    -- Local instance justification (defeq pin): expose the stored additive subgroup structures.
    letI addSubgroup : ∀ U, AddSubgroupClass (homogeneousCarrier U) (affineRing U) :=
      homogeneousCarrierAddSubgroup
    -- Local instance justification (defeq pin): expose the stored graded-ring structures.
    letI grading : ∀ U, GradedRing (sectionGrading U) := sectionGradingRing
    ∀ U : S.affineOpens, GradedAlgebra.GeneratedBy (sectionGrading U) 1

namespace DegreeOneTwist

/-- Construct degree-one twist data from affine graded models, their absolute twist
presentations, and a compatible relative twist presentation generated in degree one. -/
def ofPresentation (P : RelativeProjPresentation p)
    (affineRing : S.affineOpens → Type u)
    (homogeneousCarrier : S.affineOpens → Type u)
    (affineRingComm : ∀ U, CommRing (affineRing U))
    (homogeneousCarrierSetLike :
      ∀ U, SetLike (homogeneousCarrier U) (affineRing U))
    (homogeneousCarrierAddSubgroup :
      ∀ U, AddSubgroupClass (homogeneousCarrier U) (affineRing U))
    (sectionGrading : ∀ U : S.affineOpens, ℕ → homogeneousCarrier U)
    (sectionGradingRing :
      -- Local instance justification (defeq pin): expose the supplied affine ring structures.
      letI ring : ∀ U, CommRing (affineRing U) := affineRingComm
      -- Local instance justification (defeq pin): expose the supplied homogeneous carriers.
      letI setLike : ∀ U, SetLike (homogeneousCarrier U) (affineRing U) :=
        homogeneousCarrierSetLike
      -- Local instance justification (defeq pin): expose the supplied additive subgroup structures.
      letI addSubgroup : ∀ U, AddSubgroupClass (homogeneousCarrier U) (affineRing U) :=
        homogeneousCarrierAddSubgroup
      ∀ U, GradedRing (sectionGrading U))
    (absoluteTwist :
      -- Local instance justification (defeq pin): expose the supplied affine ring structures.
      letI ring : ∀ U, CommRing (affineRing U) := affineRingComm
      -- Local instance justification (defeq pin): expose the supplied homogeneous carriers.
      letI setLike : ∀ U, SetLike (homogeneousCarrier U) (affineRing U) :=
        homogeneousCarrierSetLike
      -- Local instance justification (defeq pin): expose the supplied additive subgroup structures.
      letI addSubgroup : ∀ U, AddSubgroupClass (homogeneousCarrier U) (affineRing U) :=
        homogeneousCarrierAddSubgroup
      -- Local instance justification (defeq pin): expose the supplied graded-ring structures.
      letI grading : ∀ U, GradedRing (sectionGrading U) := sectionGradingRing
      ∀ U, ProjTwistPresentation (sectionGrading U))
    (sectionModel :
      -- Local instance justification (defeq pin): expose the supplied affine ring structures.
      letI ring : ∀ U, CommRing (affineRing U) := affineRingComm
      -- Local instance justification (defeq pin): expose the supplied homogeneous carriers.
      letI setLike : ∀ U, SetLike (homogeneousCarrier U) (affineRing U) :=
        homogeneousCarrierSetLike
      ∀ (U : S.affineOpens) (d : ℕ),
        (P.algebra (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃
          sectionGrading U d)
    (twistPresentation :
      -- Local instance justification (defeq pin): expose the supplied affine ring structures.
      letI ring : ∀ U, CommRing (affineRing U) := affineRingComm
      -- Local instance justification (defeq pin): expose the supplied homogeneous carriers.
      letI setLike : ∀ U, SetLike (homogeneousCarrier U) (affineRing U) :=
        homogeneousCarrierSetLike
      -- Local instance justification (defeq pin): expose the supplied additive subgroup structures.
      letI addSubgroup : ∀ U, AddSubgroupClass (homogeneousCarrier U) (affineRing U) :=
        homogeneousCarrierAddSubgroup
      -- Local instance justification (defeq pin): expose the supplied graded-ring structures.
      letI grading : ∀ U, GradedRing (sectionGrading U) := sectionGradingRing
      RelativeProjTwist.Presentation P.algebra affineRing homogeneousCarrier
        sectionGrading absoluteTwist sectionModel p)
    (generatedByDegreeOne :
      -- Local instance justification (defeq pin): expose the supplied affine ring structures.
      letI ring : ∀ U, CommRing (affineRing U) := affineRingComm
      -- Local instance justification (defeq pin): expose the supplied homogeneous carriers.
      letI setLike : ∀ U, SetLike (homogeneousCarrier U) (affineRing U) :=
        homogeneousCarrierSetLike
      -- Local instance justification (defeq pin): expose the supplied additive subgroup structures.
      letI addSubgroup : ∀ U, AddSubgroupClass (homogeneousCarrier U) (affineRing U) :=
        homogeneousCarrierAddSubgroup
      -- Local instance justification (defeq pin): expose the supplied graded-ring structures.
      letI grading : ∀ U, GradedRing (sectionGrading U) := sectionGradingRing
      ∀ U : S.affineOpens, GradedAlgebra.GeneratedBy (sectionGrading U) 1) :
    DegreeOneTwist P where
  affineRing := affineRing
  homogeneousCarrier := homogeneousCarrier
  affineRingComm := affineRingComm
  homogeneousCarrierSetLike := homogeneousCarrierSetLike
  homogeneousCarrierAddSubgroup := homogeneousCarrierAddSubgroup
  sectionGrading := sectionGrading
  sectionGradingRing := sectionGradingRing
  absoluteTwist := absoluteTwist
  sectionModel := sectionModel
  twistPresentation := twistPresentation
  generatedByDegreeOne := generatedByDegreeOne

/-- The first twist in the raw twist presentation. -/
noncomputable def twistOne {P : RelativeProjPresentation p}
    (D : DegreeOneTwist P) : X.Modules :=
  -- Local instance justification (defeq pin): unpack the explicit ring data stored in `D`.
  letI : ∀ U, CommRing (D.affineRing U) := D.affineRingComm
  -- Local instance justification (defeq pin): unpack the explicit grading carrier stored in `D`.
  letI : ∀ U, SetLike (D.homogeneousCarrier U) (D.affineRing U) :=
    D.homogeneousCarrierSetLike
  -- Local instance justification (defeq pin): unpack the explicit additive grading data in `D`.
  letI : ∀ U, AddSubgroupClass (D.homogeneousCarrier U) (D.affineRing U) :=
    D.homogeneousCarrierAddSubgroup
  -- Local instance justification (defeq pin): unpack the explicit graded-ring laws stored in `D`.
  letI : ∀ U, GradedRing (D.sectionGrading U) := D.sectionGradingRing
  D.twistPresentation.twistAlgebra 1

/-- The canonical degree-one map, defined as the pullback-pushforward adjoint of the
degree-one component of the multiplicative twist map. -/
noncomputable def degreeOneMap {P : RelativeProjPresentation p} (D : DegreeOneTwist P) :
    (Scheme.Modules.pullback p).obj (P.degreePiece 1) ⟶ D.twistOne :=
  -- Local instance justification (defeq pin): unpack the explicit ring data stored in `D`.
  letI : ∀ U, CommRing (D.affineRing U) := D.affineRingComm
  -- Local instance justification (defeq pin): unpack the explicit grading carrier stored in `D`.
  letI : ∀ U, SetLike (D.homogeneousCarrier U) (D.affineRing U) :=
    D.homogeneousCarrierSetLike
  -- Local instance justification (defeq pin): unpack the explicit additive grading data in `D`.
  letI : ∀ U, AddSubgroupClass (D.homogeneousCarrier U) (D.affineRing U) :=
    D.homogeneousCarrierAddSubgroup
  -- Local instance justification (defeq pin): unpack the explicit graded-ring laws stored in `D`.
  letI : ∀ U, GradedRing (D.sectionGrading U) := D.sectionGradingRing
  ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv
    (P.degreePiece 1) D.twistOne).symm (D.twistPresentation.psi.hom 1)

/-- Thin specialization of the affine-model generation shorthand to stored twist data.
For generation over the structure sheaf, use `generatedByDegreeOne_intrinsic` with compatible
additive section models and surjective degree-zero structure maps. -/
abbrev GeneratedByDegreeOne {P : RelativeProjPresentation p} (D : DegreeOneTwist P) : Prop :=
  -- Local instance justification (defeq pin): unpack the explicit ring data stored in `D`.
  letI : ∀ U, CommRing (D.affineRing U) := D.affineRingComm
  -- Local instance justification (defeq pin): unpack the explicit grading carrier stored in `D`.
  letI : ∀ U, SetLike (D.homogeneousCarrier U) (D.affineRing U) :=
    D.homogeneousCarrierSetLike
  -- Local instance justification (defeq pin): unpack the explicit additive grading data in `D`.
  letI : ∀ U, AddSubgroupClass (D.homogeneousCarrier U) (D.affineRing U) :=
    D.homogeneousCarrierAddSubgroup
  -- Local instance justification (defeq pin): unpack the explicit graded-ring laws stored in `D`.
  letI : ∀ U, GradedRing (D.sectionGrading U) := D.sectionGradingRing
  D.twistPresentation.GeneratedByDegreeOne

/-- Degree-one twist data retain the raw twist presentation and degree-one generation law. -/
theorem spec {P : RelativeProjPresentation p} (D : DegreeOneTwist P) :
    D.GeneratedByDegreeOne :=
  D.generatedByDegreeOne

/-- The stored affine generation law yields intrinsic generation when the stored rings admit
compatible additive section models and the structure maps onto degree zero are surjective.
The raw set equivalences in `D.sectionModel` alone do not imply this conclusion. -/
theorem generatedByDegreeOne_intrinsic {P : RelativeProjPresentation p} (D : DegreeOneTwist P) :
    letI : ∀ U, CommRing (D.affineRing U) := D.affineRingComm
    letI : ∀ U, SetLike (D.homogeneousCarrier U) (D.affineRing U) :=
      D.homogeneousCarrierSetLike
    letI : ∀ U, AddSubgroupClass (D.homogeneousCarrier U) (D.affineRing U) :=
      D.homogeneousCarrierAddSubgroup
    letI : ∀ U, GradedRing (D.sectionGrading U) := D.sectionGradingRing
    ∀ (model : ∀ (U : S.affineOpens) (d : ℕ),
        (P.algebra (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+
          D.sectionGrading U d)
      (hModel : ∀ U : S.affineOpens,
        AffineOpenSectionProj.IsAffineOpenSectionModel
          (D.sectionGrading U) P.algebra U (model U))
      (hzero : ∀ U : S.affineOpens,
        Function.Surjective
          (AffineOpenSectionProj.degreeZeroStructureMap
            (D.sectionGrading U) P.algebra U (model U) (hModel U))),
      GradedAlgebraSheaf.GeneratedByDegreeOne P.algebra :=
  letI : ∀ U, CommRing (D.affineRing U) := D.affineRingComm
  letI : ∀ U, SetLike (D.homogeneousCarrier U) (D.affineRing U) :=
    D.homogeneousCarrierSetLike
  letI : ∀ U, AddSubgroupClass (D.homogeneousCarrier U) (D.affineRing U) :=
    D.homogeneousCarrierAddSubgroup
  letI : ∀ U, GradedRing (D.sectionGrading U) := D.sectionGradingRing
  fun model hModel hzero ↦
    GradedAlgebraSheaf.generatedByDegreeOne_of_affineOpenSectionModels
      P.algebra D.affineRing D.homogeneousCarrier D.sectionGrading model hModel hzero
      D.generatedByDegreeOne

/-- The canonical degree-one map is an epimorphism. -/
theorem degreeOneMap_epi {P : RelativeProjPresentation p} (D : DegreeOneTwist P) :
    Epi D.degreeOneMap := sorry

/-- The first twist is invertible under affine-local degree-one generation. -/
theorem twistOne_isInvertible {P : RelativeProjPresentation p} (D : DegreeOneTwist P) :
    Scheme.Modules.Invertible D.twistOne := by
  -- Local instance justification (defeq pin): unpack the explicit ring data stored in `D`.
  letI : ∀ U, CommRing (D.affineRing U) := D.affineRingComm
  -- Local instance justification (defeq pin): unpack the explicit grading carrier stored in `D`.
  letI : ∀ U, SetLike (D.homogeneousCarrier U) (D.affineRing U) :=
    D.homogeneousCarrierSetLike
  -- Local instance justification (defeq pin): unpack the explicit additive grading data in `D`.
  letI : ∀ U, AddSubgroupClass (D.homogeneousCarrier U) (D.affineRing U) :=
    D.homogeneousCarrierAddSubgroup
  -- Local instance justification (defeq pin): unpack the explicit graded-ring laws stored in `D`.
  letI : ∀ U, GradedRing (D.sectionGrading U) := D.sectionGradingRing
  exact RelativeProjTwist.Presentation.twist_invertible_of_generatedByDegreeOne
    P.algebra D.affineRing D.homogeneousCarrier D.sectionGrading D.absoluteTwist
      D.sectionModel D.twistPresentation D.generatedByDegreeOne 1

/-- The canonical epimorphism from the pulled-back degree-one piece onto the first twist. -/
noncomputable def quotient {P : RelativeProjPresentation p} (D : DegreeOneTwist P) :
    CategoryTheory.InvertibleQuotient
      ((Scheme.Modules.pullback p).obj (P.degreePiece 1)) where
  object := D.twistOne
  isInvertible := D.twistOne_isInvertible
  hom := D.degreeOneMap
  hom_epi := D.degreeOneMap_epi

/-- The canonical quotient has the first twist as target and the adjoint degree-one map as its
quotient morphism. -/
theorem quotient_spec {P : RelativeProjPresentation p} (D : DegreeOneTwist P) :
    D.quotient.object = D.twistOne ∧ D.quotient.hom = D.degreeOneMap := sorry

end DegreeOneTwist

end AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation
