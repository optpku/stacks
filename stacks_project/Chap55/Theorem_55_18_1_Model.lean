/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Localization.AtPrime.FractionRing
public import ReasLib.RingTheory.Localization.FractionRing.IntegralClosure.AtPrime
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Over
public import stacks_project.Chap53.Definition_53_8_1_Genus
public import stacks_project.Chap53.Lemma_53_20_12_Nodal
public import stacks_project.Chap53.Remark_53_19_8_The_quadratic_extension_associated_to_a_node_NodeAlgebra
public import stacks_project.Chap55.Definition_55_8_4_MinimalModel
public import stacks_project.Chap55.Lemma_55_8_5_Model
public import stacks_project.Chap55.Lemma_55_9_1_SpecialFiber

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
    (M : SemistableModel R K C) :=
  Over.mk (M.regularModel.base.fiberOverSpecResidueField (IsLocalRing.closedPoint R)).hom

/-- The residue-field special fibre has the canonical fibre structural morphism. -/
theorem specialFiberOverResidueField_def {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (M : SemistableModel R K C) :
    (specialFiberOverResidueField R K M).hom =
      (M.regularModel.base.fiberOverSpecResidueField (IsLocalRing.closedPoint R)).hom := sorry

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

/-- An explicit rationality witness for a scheme over a fixed field. -/
structure RationalCurve (k : Type u) [Field k] (X : SchemeOverField k) where
  /-- The projective-line isomorphism over the chosen base field. -/
  iso : X ≅ ProjectiveSpace.schemeOver k 1

/-- Construct a rational-curve witness from its projective-line isomorphism. -/
def RationalCurve.ofIso {k : Type u} [Field k] {X : SchemeOverField k}
    (e : X ≅ ProjectiveSpace.schemeOver k 1) : RationalCurve k X :=
  { iso := e }

/-- The rational-curve witness is equivalent to an isomorphism with the projective line over `k`. -/
theorem RationalCurve_iff {k : Type u} [Field k] (X : SchemeOverField k) :
    Nonempty (RationalCurve k X) ↔
      Nonempty (X ≅ ProjectiveSpace.schemeOver k 1) := sorry

/-- Concrete component, rationality, and exact nodal-incidence data for a cycle of rational
curves over the residue field of the special fibre. -/
structure RationalCycleWitness (k : Type u) [Field k] (X : SchemeOverField k) where
  /-- The number of irreducible components in the cycle. -/
  n : ℕ
  /-- A cycle contains at least one irreducible component. -/
  n_pos : 0 < n
  /-- An enumeration of all irreducible components. -/
  components : Fin n ≃ irreducibleComponents X.left
  /-- Every enumerated component is a rational curve over the residue field. -/
  rational : ∀ i, RationalCurve k
    (Over.mk (X.left.irreducibleComponentSubschemeι (components i) ≫ X.hom))
  /-- The cyclic successor permutation on the components. -/
  next : Equiv.Perm (Fin n)
  /-- Iterating the successor reaches every component from every other component. -/
  next_transitive : ∀ i j, ∃ r : ℕ, r < n ∧ (next^[r]) i = j
  /-- The nodal intersection following each component in the cycle. -/
  node : Fin n → X.left
  /-- Distinct cycle edges have distinct nodes. -/
  node_injective : Function.Injective node
  /-- Each displayed intersection point is nodal. -/
  node_nodal : ∀ i, IsNodalLocalRing (X.left.presheaf.stalk (node i))
  /-- The node following a component lies on that component. -/
  node_mem : ∀ i, node i ∈ (components i : Set X.left)
  /-- The same node lies on the successor component. -/
  node_mem_next : ∀ i, node i ∈ (components (next i) : Set X.left)
  /-- The intersection of two distinct components consists exactly of their recorded cycle
  nodes, so there are no additional intersections or parallel unrecorded nodes. -/
  component_intersection : ∀ i j, i ≠ j →
    (components i : Set X.left) ∩ (components j : Set X.left) =
      {x | (next i = j ∧ x = node i) ∨ (next j = i ∧ x = node j)}

/-- Construct a rational-cycle witness from its component, rationality, and incidence data. -/
def RationalCycleWitness.ofData {k : Type u} [Field k] {X : SchemeOverField k}
    (n : ℕ) (n_pos : 0 < n)
    (components : Fin n ≃ irreducibleComponents X.left)
    (h_rational : ∀ i, RationalCurve k
      (Over.mk (X.left.irreducibleComponentSubschemeι (components i) ≫ X.hom)))
    (next : Equiv.Perm (Fin n))
    (h_next : ∀ i j, ∃ r : ℕ, r < n ∧ (next^[r]) i = j)
    (node : Fin n → X.left)
    (h_node_injective : Function.Injective node)
    (h_node_nodal : ∀ i, IsNodalLocalRing (X.left.presheaf.stalk (node i)))
    (h_node_mem : ∀ i, node i ∈ (components i : Set X.left))
    (h_node_mem_next : ∀ i, node i ∈ (components (next i) : Set X.left))
    (h_intersection : ∀ i j, i ≠ j →
      (components i : Set X.left) ∩ (components j : Set X.left) =
        {x | (next i = j ∧ x = node i) ∨ (next j = i ∧ x = node j)}) :
    RationalCycleWitness k X :=
  { n := n
    n_pos := n_pos
    components := components
    rational := h_rational
    next := next
    next_transitive := h_next
    node := node
    node_injective := h_node_injective
    node_nodal := h_node_nodal
    node_mem := h_node_mem
    node_mem_next := h_node_mem_next
    component_intersection := h_intersection }

/-- The two source alternatives for the special fibre of a minimal genus-one model. -/
def GenusOneMinimalFiberShape (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (M : SemistableModel R K C) : Prop :=
  IsMinimalModel M.regularModel.base ∧
    (SmoothGenusOneFiber R K M ∨
      Nonempty (RationalCycleWitness
        ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))
        (specialFiberOverResidueField R K M)))

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
            (specialFiberOverResidueField R K M))) := sorry

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

/-- The branch-level shape bridge unfolds to the selected model's minimal special-fibre shape. -/
theorem SemistableReductionBranch.genusOneShape_iff {R K K' : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field K'] [Algebra K K'] [Algebra R K'] [IsScalarTower R K K']
    {C : SchemeOverField K'} (m : MaximalSpectrum (integralClosure R K'))
    (B : SemistableReductionBranch R K K' C m) :
    SemistableReductionBranch.genusOneShape m B ↔
      @GenusOneMinimalFiberShape (Localization.AtPrime m.asIdeal) K'
        inferInstance inferInstance B.localDVR inferInstance B.localAlgebra B.localFraction C
          B.curve B.smooth B.projective B.model := sorry

end AlgebraicGeometry.Scheme.Hom
