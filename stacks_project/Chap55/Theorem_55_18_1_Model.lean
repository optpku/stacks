/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Curve.SemistableReduction.Model

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u

#check (AlgebraicGeometry.Scheme.Hom.RationalCurve :
  ∀ (k : Type u) [Field k] (X : SchemeOverField k), Type (u))

#check (AlgebraicGeometry.Scheme.Hom.RationalCurve.ofIso :
  ∀ {k : Type u} [Field k] {X : SchemeOverField k}
    (iso : X ≅ ProjectiveSpace.schemeOver k 1),
    RationalCurve k X)

#check (AlgebraicGeometry.Scheme.Hom.RationalCurve_iff :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k),
    Nonempty (RationalCurve k X) ↔
      Nonempty (X ≅ ProjectiveSpace.schemeOver k 1))

#check (AlgebraicGeometry.Scheme.Hom.RationalCycleWitness.normalizedComponentOver :
  ∀ {k : Type u} [Field k]
    (X : SchemeOverField k) [IsNoetherian X.left]
    (component : irreducibleComponents X.left),
    SchemeOverField k)

#check (AlgebraicGeometry.Scheme.Hom.RationalCycleWitness.normalizedComponentTo :
  ∀ {k : Type u} [Field k]
    (X : SchemeOverField k) [IsNoetherian X.left]
    (component : irreducibleComponents X.left),
    (RationalCycleWitness.normalizedComponentOver X component).left ⟶ X.left)

#check (AlgebraicGeometry.Scheme.Hom.RationalCycleWitness.projectiveComponentTo :
  ∀ {k : Type u} [Field k]
    (X : SchemeOverField k) [IsNoetherian X.left]
    (component : irreducibleComponents X.left)
    (rational : RationalCurve k (RationalCycleWitness.normalizedComponentOver X component)),
    (ProjectiveSpace.schemeOver k 1).left ⟶ X.left)

#check (AlgebraicGeometry.Scheme.Hom.RationalCycleWitness.projectiveComponentTo_apply :
  ∀ {k : Type u} [Field k]
    (X : SchemeOverField k) [IsNoetherian X.left]
    (component : irreducibleComponents X.left)
    (rational : RationalCurve k (RationalCycleWitness.normalizedComponentOver X component))
    (point : ProjectiveSpectrum (ProjectiveSpace.grading k 1)),
    RationalCycleWitness.projectiveComponentTo X component rational point =
      RationalCycleWitness.normalizedComponentTo X component (rational.iso.inv.left point))

#check (AlgebraicGeometry.Scheme.Hom.RationalCycleWitness :
  ∀ (k : Type u) [Field k] (X : SchemeOverField k)
    [noetherian : IsNoetherian X.left], Type (u))

#check (AlgebraicGeometry.Scheme.Hom.RationalCycleWitness.ofData :
  ∀ {k : Type u} [Field k] {X : SchemeOverField k}
    [noetherian : IsNoetherian X.left]
    (reduced : IsReduced X.left) (atWorstNodal : SchemeOverField.atWorstNodal X)
    (n : ℕ) (n_pos : 0 < n)
    (components : Fin n ≃ irreducibleComponents X.left)
    (rational : ∀ index, RationalCurve k (RationalCycleWitness.normalizedComponentOver X (components index)))
    (next : Equiv.Perm (Fin n))
    (next_transitive : ∀ first last, ∃ step : ℕ, step < n ∧ (next^[step]) first = last)
    (node : Fin n → X.left) (node_injective : Function.Injective node)
    (node_nodal : ∀ index, SchemeOverField.isNode X (node index))
    (nodes_exhaustive : ∀ point, SchemeOverField.isNode X point ↔
      ∃ index, node index = point)
    (node_mem : ∀ index, node index ∈ (components index : Set X.left))
    (node_mem_next : ∀ index, node index ∈ (components (next index) : Set X.left))
    (branchLeft : Fin n → ProjectiveSpectrum (ProjectiveSpace.grading k 1))
    (branchRight : Fin n → ProjectiveSpectrum (ProjectiveSpace.grading k 1))
    (branches_distinct : ∀ index,
      (index, branchLeft index) ≠ (next index, branchRight index))
    (branch_fiber : ∀ index
      (branch : Fin n × ProjectiveSpectrum (ProjectiveSpace.grading k 1)),
      RationalCycleWitness.projectiveComponentTo X (components branch.1) (rational branch.1)
        branch.2 = node index ↔
        branch = (index, branchLeft index) ∨ branch = (next index, branchRight index))
    (component_intersection : ∀ first last, first ≠ last →
      (components first : Set X.left) ∩ (components last : Set X.left) =
        {point | (next first = last ∧ point = node first) ∨
          (next last = first ∧ point = node last)}),
    RationalCycleWitness k X)

#check (AlgebraicGeometry.Scheme.Hom.RationalCycleWitness.spec :
  ∀ {k : Type u} [Field k] {X : SchemeOverField k}
    [noetherian : IsNoetherian X.left] (cycle : RationalCycleWitness k X),
    IsReduced X.left ∧ SchemeOverField.atWorstNodal X ∧ 0 < cycle.n ∧
      (∀ index, Nonempty (RationalCycleWitness.normalizedComponentOver X (cycle.components index) ≅
        ProjectiveSpace.schemeOver k 1)) ∧
      (∀ first last, ∃ step : ℕ,
        step < cycle.n ∧ (cycle.next^[step]) first = last) ∧
      Function.Injective cycle.node ∧
      (∀ index, SchemeOverField.isNode X (cycle.node index)) ∧
      (∀ point, SchemeOverField.isNode X point ↔ ∃ index, cycle.node index = point) ∧
      (∀ index, cycle.node index ∈ (cycle.components index : Set X.left)) ∧
      (∀ index, cycle.node index ∈ (cycle.components (cycle.next index) : Set X.left)) ∧
      (∀ index,
        (index, cycle.branchLeft index) ≠ (cycle.next index, cycle.branchRight index)) ∧
      (∀ index (branch : Fin cycle.n × ProjectiveSpectrum (ProjectiveSpace.grading k 1)),
        RationalCycleWitness.projectiveComponentTo X (cycle.components branch.1)
          (cycle.rational branch.1) branch.2 = cycle.node index ↔
          branch = (index, cycle.branchLeft index) ∨
            branch = (cycle.next index, cycle.branchRight index)) ∧
      (∀ first last, first ≠ last →
        (cycle.components first : Set X.left) ∩ (cycle.components last : Set X.left) =
          {point | (cycle.next first = last ∧ point = cycle.node first) ∨
            (cycle.next last = first ∧ point = cycle.node last)}))

#check (AlgebraicGeometry.Scheme.Hom.SemistableModel :
  ∀ (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom], Type (u + 1))

#check (AlgebraicGeometry.Scheme.Hom.SemistableModel.ofRegularModel :
  ∀ {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (M : RegularModel R K C) (h_nodal : AtWorstNodal M.base),
    SemistableModel R K C)

#check (AlgebraicGeometry.Scheme.Hom.SemistableModel.isMinimal :
  ∀ (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (M : SemistableModel R K C),
    Prop)

#check (AlgebraicGeometry.Scheme.Hom.SemistableModel.isMinimal_iff :
  ∀ {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (M : SemistableModel R K C),
    SemistableModel.isMinimal R K M ↔ IsMinimalModel M.regularModel.base)

#check (AlgebraicGeometry.Scheme.Hom.hasSemistableReduction :
  ∀ (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom],
    Prop)

#check (AlgebraicGeometry.Scheme.Hom.hasSemistableReduction_iff :
  ∀ {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom],
    hasSemistableReduction R K C ↔
      ∃ M : RegularModel R K C, AtWorstNodal M.base)

#check (AlgebraicGeometry.Scheme.Hom.SemistableReductionBranch :
  ∀ (R K K' : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field K'] [Algebra K K'] [Algebra R K'] [IsScalarTower R K K']
    (C : SchemeOverField K') (m : MaximalSpectrum (integralClosure R K')), Type (u + 1))

#check (AlgebraicGeometry.Scheme.Hom.SemistableReductionBranch.ofData :
  ∀ {R K K' : Type u} [CommRing R] [IsDomain R]
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
        h_curve h_smooth h_projective),
    SemistableReductionBranch R K K' C m)

#check (AlgebraicGeometry.Scheme.Hom.hasSemistableReductionAtMaximal :
  ∀ (R K K' : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field K'] [Algebra K K'] [Algebra R K'] [IsScalarTower R K K']
    (C : SchemeOverField K'),
    Prop)

#check (AlgebraicGeometry.Scheme.Hom.hasSemistableReductionAtMaximal_iff :
  ∀ {R K K' : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field K'] [Algebra K K'] [Algebra R K'] [IsScalarTower R K K']
    (C : SchemeOverField K'),
    hasSemistableReductionAtMaximal R K K' C ↔
      ∀ m : MaximalSpectrum (integralClosure R K'),
        Nonempty (SemistableReductionBranch R K K' C m))

#check (AlgebraicGeometry.Scheme.Hom.specialFiber :
  ∀ {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)),
    Scheme.{u})

#check (AlgebraicGeometry.Scheme.Hom.specialFiber_def :
  ∀ {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (M : SemistableModel R K C),
    M.regularModel.base.specialFiber =
      M.regularModel.base.fiber (IsLocalRing.closedPoint R))

#check (AlgebraicGeometry.Scheme.Hom.specialFiberOverResidueField :
  ∀ (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (M : SemistableModel R K C),
    SchemeOverField ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)))

#check (AlgebraicGeometry.Scheme.Hom.specialFiberOverResidueField_def :
  ∀ {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (M : SemistableModel R K C),
    (specialFiberOverResidueField R K M).hom =
      (M.regularModel.base.fiberOverSpecResidueField (IsLocalRing.closedPoint R)).hom)

#check (AlgebraicGeometry.Scheme.Hom.SemistableModel.specialFiber_isNoetherian :
  ∀ {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (model : SemistableModel R K C),
    IsNoetherian (specialFiberOverResidueField R K model).left)

#check (AlgebraicGeometry.Scheme.Hom.SmoothGenusOneFiber :
  ∀ (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (M : SemistableModel R K C),
    Prop)

#check (AlgebraicGeometry.Scheme.Hom.SmoothGenusOneFiber_iff :
  ∀ {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (M : SemistableModel R K C),
    SmoothGenusOneFiber R K M ↔
      let X := specialFiberOverResidueField R K M
      ∃ (h_curve : Curve X) (h_smooth : Smooth X.hom) (h_projective : Projective X.hom)
        (h_proper : IsProper X.hom)
        (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
        @SchemeOverField.genus _ inferInstance X h_proper
          (@topologicalKrullDim_eq_one _ inferInstance X h_curve) hΓ = 1)

#check (AlgebraicGeometry.Scheme.Hom.GenusOneMinimalFiberShape :
  ∀ (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (M : SemistableModel R K C),
    Prop)

#check (AlgebraicGeometry.Scheme.Hom.GenusOneMinimalFiberShape_iff :
  ∀ {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (M : SemistableModel R K C),
    GenusOneMinimalFiberShape R K M ↔
      IsMinimalModel M.regularModel.base ∧
        (SmoothGenusOneFiber R K M ∨
          Nonempty (RationalCycleWitness
            ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))
            (specialFiberOverResidueField R K M)
            (noetherian := SemistableModel.specialFiber_isNoetherian M))))

#check (AlgebraicGeometry.Scheme.Hom.SemistableReductionBranch.genusOneShape :
  ∀ {R K K' : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field K'] [Algebra K K'] [Algebra R K'] [IsScalarTower R K K']
    {C : SchemeOverField K'} (m : MaximalSpectrum (integralClosure R K'))
    (B : SemistableReductionBranch R K K' C m),
    Prop)

#check (AlgebraicGeometry.Scheme.Hom.SemistableReductionBranch.isMinimal :
  ∀ {R K K' : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field K'] [Algebra K K'] [Algebra R K'] [IsScalarTower R K K']
    {C : SchemeOverField K'} (m : MaximalSpectrum (integralClosure R K'))
    (B : SemistableReductionBranch R K K' C m),
    Prop)

#check (AlgebraicGeometry.Scheme.Hom.SemistableReductionBranch.isMinimal_iff :
  ∀ {R K K' : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field K'] [Algebra K K'] [Algebra R K'] [IsScalarTower R K K']
    {C : SchemeOverField K'} (m : MaximalSpectrum (integralClosure R K'))
    (B : SemistableReductionBranch R K K' C m),
    SemistableReductionBranch.isMinimal m B ↔
      @SemistableModel.isMinimal (Localization.AtPrime m.asIdeal) K'
        inferInstance inferInstance B.localDVR inferInstance B.localAlgebra B.localFraction C
          B.curve B.smooth B.projective B.model)

#check (AlgebraicGeometry.Scheme.Hom.SemistableReductionBranch.genusOneShape_iff :
  ∀ {R K K' : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field K'] [Algebra K K'] [Algebra R K'] [IsScalarTower R K K']
    {C : SchemeOverField K'} (m : MaximalSpectrum (integralClosure R K'))
    (B : SemistableReductionBranch R K K' C m),
    SemistableReductionBranch.genusOneShape m B ↔
      @GenusOneMinimalFiberShape (Localization.AtPrime m.asIdeal) K'
        inferInstance inferInstance B.localDVR inferInstance B.localAlgebra B.localFraction C
          B.curve B.smooth B.projective B.model)

#check (AlgebraicGeometry.Scheme.Hom.SemistableReductionBranch.allMinimalModelsHaveGenusOneShape :
  ∀ {R K K' : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field K'] [Algebra K K'] [Algebra R K'] [IsScalarTower R K K']
    {C : SchemeOverField K'} (m : MaximalSpectrum (integralClosure R K'))
    (branch : SemistableReductionBranch R K K' C m), Prop)

#check (AlgebraicGeometry.Scheme.Hom.SemistableReductionBranch.allMinimalModelsHaveGenusOneShape_iff :
  ∀ {R K K' : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field K'] [Algebra K K'] [Algebra R K'] [IsScalarTower R K K']
    {C : SchemeOverField K'} (m : MaximalSpectrum (integralClosure R K'))
    (branch : SemistableReductionBranch R K K' C m),
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
              Nonempty (Over.mk modelBase ≅ Over.mk selectedBase))
