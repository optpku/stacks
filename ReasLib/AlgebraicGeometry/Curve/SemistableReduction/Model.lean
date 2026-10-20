/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Localization.AtPrime.FractionRing
public import ReasLib.RingTheory.Localization.FractionRing.IntegralClosure.AtPrime
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Basic
public import ReasLib.AlgebraicGeometry.Curve.RationalCycle
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AtWorstNodal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.MinimalModel
public import ReasLib.AlgebraicGeometry.Scheme.Model.Regular.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A semistable model consists of a regular model whose structural morphism is at worst nodal. -/
structure SemistableModel (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom] where
  /-- The underlying regular model. -/
  regularModel : RegularModel R K C
  /-- The model morphism is at worst nodal. -/
  atWorstNodal : AtWorstNodal regularModel.base

/-- Construct a semistable model from a regular model and an at-worst-nodal proof. -/
def SemistableModel.ofRegularModel {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (M : RegularModel R K C) (h_nodal : AtWorstNodal M.base) :
    SemistableModel R K C :=
  { regularModel := M
    atWorstNodal := h_nodal }

/-- Minimality of the regular model underlying a semistable model. -/
def SemistableModel.isMinimal (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (M : SemistableModel R K C) : Prop :=
  IsMinimalModel M.regularModel.base

/-- Semistable-model minimality is minimality of its underlying regular-model morphism. -/
theorem SemistableModel.isMinimal_iff {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (M : SemistableModel R K C) :
    SemistableModel.isMinimal R K M ↔ IsMinimalModel M.regularModel.base := sorry

/-- A smooth projective curve over a fraction field has semistable reduction when a
semistable model exists over the discrete valuation ring. -/
def hasSemistableReduction (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom] : Prop :=
  Nonempty (SemistableModel R K C)

/-- The semistable-reduction predicate is witnessed by a regular model with an at-worst-nodal
structural morphism. -/
theorem hasSemistableReduction_iff {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom] :
    hasSemistableReduction R K C ↔
      ∃ M : RegularModel R K C, AtWorstNodal M.base := sorry

/-- A branch of semistable reduction over a maximal localization of an integral closure. -/
structure SemistableReductionBranch (R K K' : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field K'] [Algebra K K'] [Algebra R K'] [IsScalarTower R K K']
    (C : SchemeOverField K') (m : MaximalSpectrum (integralClosure R K')) where
  /-- The base-changed curve is a curve over the extension field. -/
  curve : Curve C
  /-- The base-changed curve is smooth. -/
  smooth : Smooth C.hom
  /-- The base-changed curve is projective. -/
  projective : Projective C.hom
  /-- The localized integral closure is a discrete valuation ring. -/
  localDVR : IsDiscreteValuationRing (Localization.AtPrime m.asIdeal)
  /-- The selected localization is an extension of the original discrete valuation ring. -/
  extension : @IsExtensionOfDiscreteValuationRings R (Localization.AtPrime m.asIdeal)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance localDVR
  /-- The chosen fraction-field algebra of the local branch. -/
  localAlgebra : Algebra (Localization.AtPrime m.asIdeal) K'
  /-- The local fraction-field map agrees with the given map from the original DVR. -/
  localAlgebra_compatible : ∀ r : R,
    (@algebraMap (Localization.AtPrime m.asIdeal) K' _ _ localAlgebra)
      (algebraMap R (Localization.AtPrime m.asIdeal) r) = algebraMap R K' r
  /-- The local fraction-field map extends the canonical inclusion of the integral closure. -/
  localAlgebra_extendsIntegralClosure : ∀ a : integralClosure R K',
    (@algebraMap (Localization.AtPrime m.asIdeal) K' _ _ localAlgebra)
      (algebraMap (integralClosure R K') (Localization.AtPrime m.asIdeal) a) =
        algebraMap (integralClosure R K') K' a
  /-- The extension field is a fraction field of the local branch. -/
  localFraction : IsFractionRing (Localization.AtPrime m.asIdeal) K'
  /-- A semistable model over the selected local branch. -/
  model : @SemistableModel (Localization.AtPrime m.asIdeal) K'
    inferInstance inferInstance localDVR inferInstance localAlgebra localFraction C
      curve smooth projective

/-- Construct a maximal-localization branch from its local structures and semistable model. -/
def SemistableReductionBranch.ofData {R K K' : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field K'] [Algebra K K'] [Algebra R K'] [IsScalarTower R K K']
    (C : SchemeOverField K') (m : MaximalSpectrum (integralClosure R K'))
    (h_curve : Curve C) (h_smooth : Smooth C.hom) (h_projective : Projective C.hom)
    (h_localDVR : IsDiscreteValuationRing (Localization.AtPrime m.asIdeal))
    (h_extension : @IsExtensionOfDiscreteValuationRings R (Localization.AtPrime m.asIdeal)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance h_localDVR)
    (h_localAlgebra : Algebra (Localization.AtPrime m.asIdeal) K')
    (h_localAlgebra_compatible : ∀ r : R,
      (@algebraMap (Localization.AtPrime m.asIdeal) K' _ _ h_localAlgebra)
        (algebraMap R (Localization.AtPrime m.asIdeal) r) = algebraMap R K' r)
    (h_localAlgebra_extendsIntegralClosure : ∀ a : integralClosure R K',
      (@algebraMap (Localization.AtPrime m.asIdeal) K' _ _ h_localAlgebra)
        (algebraMap (integralClosure R K') (Localization.AtPrime m.asIdeal) a) =
          algebraMap (integralClosure R K') K' a)
    (h_localFraction : IsFractionRing (Localization.AtPrime m.asIdeal) K')
    (M : @SemistableModel (Localization.AtPrime m.asIdeal) K'
      inferInstance inferInstance h_localDVR inferInstance h_localAlgebra h_localFraction C
        h_curve h_smooth h_projective) :
    SemistableReductionBranch R K K' C m :=
  { curve := h_curve
    smooth := h_smooth
    projective := h_projective
    localDVR := h_localDVR
    extension := h_extension
    localAlgebra := h_localAlgebra
    localAlgebra_compatible := h_localAlgebra_compatible
    localAlgebra_extendsIntegralClosure := h_localAlgebra_extendsIntegralClosure
    localFraction := h_localFraction
    model := M }

/-- Semistable reduction over every maximal localization of the integral closure of `R` in `K'`.
The branch witness records the local DVR, its fraction-field identification, and the model. -/
def hasSemistableReductionAtMaximal (R K K' : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field K'] [Algebra K K'] [Algebra R K'] [IsScalarTower R K K']
    (C : SchemeOverField K') : Prop :=
  ∀ m : MaximalSpectrum (integralClosure R K'),
    Nonempty (SemistableReductionBranch R K K' C m)

/-- The maximal-branch predicate exposes the chosen branch model and local field data. -/
theorem hasSemistableReductionAtMaximal_iff {R K K' : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field K'] [Algebra K K'] [Algebra R K'] [IsScalarTower R K K']
    (C : SchemeOverField K') :
    hasSemistableReductionAtMaximal R K K' C ↔
      ∀ m : MaximalSpectrum (integralClosure R K'),
        Nonempty (SemistableReductionBranch R K K' C m) := sorry

/-- The scheme-theoretic special fibre of a semistable model over a local base. -/
noncomputable def specialFiber (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (M : SemistableModel R K C) : Scheme :=
  M.regularModel.base.fiber (IsLocalRing.closedPoint R)

/-- The named special fibre is the fibre over the closed point of the local base. -/
theorem specialFiber_def {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (M : SemistableModel R K C) :
    specialFiber R K M =
      M.regularModel.base.fiber (IsLocalRing.closedPoint R) := sorry

/-- The special fibre with its canonical structure over the residue field of the local base. -/
noncomputable def specialFiberOverResidueField (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (M : SemistableModel R K C) :
    SchemeOverField ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) :=
  Over.mk (M.regularModel.base.fiberOverSpecResidueField (IsLocalRing.closedPoint R)).hom

/-- The residue-field special fibre has the canonical fibre structural morphism. -/
theorem specialFiberOverResidueField_def {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (M : SemistableModel R K C) :
    (specialFiberOverResidueField R K M).hom =
      (M.regularModel.base.fiberOverSpecResidueField (IsLocalRing.closedPoint R)).hom := sorry

/-- The special fibre of a supplied semistable model is a Noetherian scheme. -/
theorem SemistableModel.specialFiber_isNoetherian {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (model : SemistableModel R K C) :
    IsNoetherian (specialFiberOverResidueField R K model).left := sorry

/-- A local semistable model has smooth genus-one special fibre when its canonical fibre over the
residue field is a smooth projective curve with constant global functions and genus one. -/
def SmoothGenusOneFiber (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (M : SemistableModel R K C) : Prop :=
  let X := specialFiberOverResidueField R K M
  ∃ (h_curve : Curve X) (h_smooth : Smooth X.hom) (h_projective : Projective X.hom)
    (h_proper : IsProper X.hom)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
    @SchemeOverField.genus _ inferInstance X h_proper
      (@topologicalKrullDim_eq_one _ inferInstance X h_curve) hΓ = 1

/-- The smooth-genus-one predicate exposes all properties of the residue-field special fibre. -/
theorem SmoothGenusOneFiber_iff {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (M : SemistableModel R K C) :
    SmoothGenusOneFiber R K M ↔
      let X := specialFiberOverResidueField R K M
      ∃ (h_curve : Curve X) (h_smooth : Smooth X.hom) (h_projective : Projective X.hom)
        (h_proper : IsProper X.hom)
        (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
        @SchemeOverField.genus _ inferInstance X h_proper
          (@topologicalKrullDim_eq_one _ inferInstance X h_curve) hΓ = 1 := sorry

/-- A minimal semistable model has either smooth genus-one special fibre or a rational cycle. -/
def GenusOneMinimalFiberShape (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (M : SemistableModel R K C) : Prop :=
  IsMinimalModel M.regularModel.base ∧
    (SmoothGenusOneFiber R K M ∨
      Nonempty (RationalCycleWitness
        ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))
        (specialFiberOverResidueField R K M)
        (noetherian := SemistableModel.specialFiber_isNoetherian M)))

/-- The genus-one minimal-fibre predicate exposes the minimality and smooth-versus-cycle split. -/
theorem GenusOneMinimalFiberShape_iff {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (M : SemistableModel R K C) :
    GenusOneMinimalFiberShape R K M ↔
      IsMinimalModel M.regularModel.base ∧
        (SmoothGenusOneFiber R K M ∨
          Nonempty (RationalCycleWitness
            ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))
            (specialFiberOverResidueField R K M)
            (noetherian := SemistableModel.specialFiber_isNoetherian M))) := sorry

/-- The genus-one special-fibre shape attached to a maximal-localization branch. -/
def SemistableReductionBranch.genusOneShape {R K K' : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field K'] [Algebra K K'] [Algebra R K'] [IsScalarTower R K K']
    {C : SchemeOverField K'} (m : MaximalSpectrum (integralClosure R K'))
    (B : SemistableReductionBranch R K K' C m) : Prop :=
  @GenusOneMinimalFiberShape (Localization.AtPrime m.asIdeal) K'
    inferInstance inferInstance B.localDVR inferInstance B.localAlgebra B.localFraction C
      B.curve B.smooth B.projective B.model

/-- Minimality of the semistable model stored by a maximal-localization branch. -/
def SemistableReductionBranch.isMinimal {R K K' : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field K'] [Algebra K K'] [Algebra R K'] [IsScalarTower R K K']
    {C : SchemeOverField K'} (m : MaximalSpectrum (integralClosure R K'))
    (B : SemistableReductionBranch R K K' C m) : Prop :=
  @SemistableModel.isMinimal (Localization.AtPrime m.asIdeal) K'
    inferInstance inferInstance B.localDVR inferInstance B.localAlgebra B.localFraction C
      B.curve B.smooth B.projective B.model

/-- Branch minimality is exactly minimality of the branch's stored model morphism. -/
theorem SemistableReductionBranch.isMinimal_iff {R K K' : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field K'] [Algebra K K'] [Algebra R K'] [IsScalarTower R K K']
    {C : SchemeOverField K'} (m : MaximalSpectrum (integralClosure R K'))
    (B : SemistableReductionBranch R K K' C m) :
    SemistableReductionBranch.isMinimal m B ↔
      @SemistableModel.isMinimal (Localization.AtPrime m.asIdeal) K'
        inferInstance inferInstance B.localDVR inferInstance B.localAlgebra B.localFraction C
          B.curve B.smooth B.projective B.model := sorry

/-- A branch has genus-one shape exactly when its selected model has minimal genus-one fibre shape. -/
theorem SemistableReductionBranch.genusOneShape_iff {R K K' : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field K'] [Algebra K K'] [Algebra R K'] [IsScalarTower R K K']
    {C : SchemeOverField K'} (m : MaximalSpectrum (integralClosure R K'))
    (B : SemistableReductionBranch R K K' C m) :
    SemistableReductionBranch.genusOneShape m B ↔
      @GenusOneMinimalFiberShape (Localization.AtPrime m.asIdeal) K'
        inferInstance inferInstance B.localDVR inferInstance B.localAlgebra B.localFraction C
          B.curve B.smooth B.projective B.model := sorry

/-- Every minimal regular model over a selected branch is semistable, has the genus-one
special-fibre alternatives, and is isomorphic over the local base to the selected model. -/
def SemistableReductionBranch.allMinimalModelsHaveGenusOneShape {R K K' : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field K'] [Algebra K K'] [Algebra R K'] [IsScalarTower R K K']
    {C : SchemeOverField K'} (m : MaximalSpectrum (integralClosure R K'))
    (branch : SemistableReductionBranch R K K' C m) : Prop :=
  ∀ model : @RegularModel (Localization.AtPrime m.asIdeal) K'
      inferInstance inferInstance branch.localDVR inferInstance branch.localAlgebra
        branch.localFraction C branch.curve branch.smooth branch.projective,
    let modelBase := @RegularModel.base (Localization.AtPrime m.asIdeal) K'
      inferInstance inferInstance branch.localDVR inferInstance branch.localAlgebra
        branch.localFraction C branch.curve branch.smooth branch.projective model
    let selectedModel := @SemistableModel.regularModel (Localization.AtPrime m.asIdeal) K'
      inferInstance inferInstance branch.localDVR inferInstance branch.localAlgebra
        branch.localFraction C branch.curve branch.smooth branch.projective branch.model
    let selectedBase := @RegularModel.base (Localization.AtPrime m.asIdeal) K'
      inferInstance inferInstance branch.localDVR inferInstance branch.localAlgebra
        branch.localFraction C branch.curve branch.smooth branch.projective selectedModel
    @IsMinimalModel (Localization.AtPrime m.asIdeal) inferInstance inferInstance
      branch.localDVR _ modelBase →
      ∃ nodal : AtWorstNodal modelBase,
        @GenusOneMinimalFiberShape (Localization.AtPrime m.asIdeal) K'
      inferInstance inferInstance branch.localDVR inferInstance branch.localAlgebra
        branch.localFraction C branch.curve branch.smooth branch.projective
          (@SemistableModel.ofRegularModel (Localization.AtPrime m.asIdeal) K'
      inferInstance inferInstance branch.localDVR inferInstance branch.localAlgebra
        branch.localFraction C branch.curve branch.smooth branch.projective model nodal) ∧
          Nonempty (Over.mk modelBase ≅ Over.mk selectedBase)

/-- The universal minimal-model predicate includes nodality, the complete fibre alternatives,
and an isomorphism over the local base to the selected model. -/
theorem SemistableReductionBranch.allMinimalModelsHaveGenusOneShape_iff {R K K' : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field K'] [Algebra K K'] [Algebra R K'] [IsScalarTower R K K']
    {C : SchemeOverField K'} (m : MaximalSpectrum (integralClosure R K'))
    (branch : SemistableReductionBranch R K K' C m) :
    SemistableReductionBranch.allMinimalModelsHaveGenusOneShape m branch ↔
      ∀ model : @RegularModel (Localization.AtPrime m.asIdeal) K'
          inferInstance inferInstance branch.localDVR inferInstance branch.localAlgebra
            branch.localFraction C branch.curve branch.smooth branch.projective,
        let modelBase := @RegularModel.base (Localization.AtPrime m.asIdeal) K'
          inferInstance inferInstance branch.localDVR inferInstance branch.localAlgebra
            branch.localFraction C branch.curve branch.smooth branch.projective model
        let selectedModel := @SemistableModel.regularModel (Localization.AtPrime m.asIdeal) K'
          inferInstance inferInstance branch.localDVR inferInstance branch.localAlgebra
            branch.localFraction C branch.curve branch.smooth branch.projective branch.model
        let selectedBase := @RegularModel.base (Localization.AtPrime m.asIdeal) K'
          inferInstance inferInstance branch.localDVR inferInstance branch.localAlgebra
            branch.localFraction C branch.curve branch.smooth branch.projective selectedModel
        @IsMinimalModel (Localization.AtPrime m.asIdeal) inferInstance inferInstance
      branch.localDVR _ modelBase →
          ∃ nodal : AtWorstNodal modelBase,
            @GenusOneMinimalFiberShape (Localization.AtPrime m.asIdeal) K'
          inferInstance inferInstance branch.localDVR inferInstance branch.localAlgebra
            branch.localFraction C branch.curve branch.smooth branch.projective
              (@SemistableModel.ofRegularModel (Localization.AtPrime m.asIdeal) K'
          inferInstance inferInstance branch.localDVR inferInstance branch.localAlgebra
            branch.localFraction C branch.curve branch.smooth branch.projective model nodal) ∧
              Nonempty (Over.mk modelBase ≅ Over.mk selectedBase) := Iff.rfl

end AlgebraicGeometry.Scheme.Hom
