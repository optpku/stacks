module

public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import ReasLib.RingTheory.RingHom.FaithfullyFlat.Approximation

@[expose] public section

-- Keep native instance search for the residue-field faithfully-flat proof.
set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency true

universe u v w

namespace RingHom.FinitePresentation

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable {f : R →+* A} {g : A →+* B}

/-- Finite presentation descends from a composite along a faithfully flat,
finitely presented second map. -/
@[stacks 02KK]
theorem of_comp_of_faithfullyFlat_of_finitePresentation
    (hcomp : (g.comp f).FinitePresentation) (hfaithfullyFlat : g.FaithfullyFlat)
    (hfinitePresentation : g.FinitePresentation) :
    f.FinitePresentation := sorry

end RingHom.FinitePresentation

noncomputable section

universe t s

open MvPolynomial
open scoped TensorProduct

namespace Algebra.SubmersivePresentation.CoefficientModel

variable (R : Type u) {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable {ι : Type t} {σ : Type s}
variable [Finite ι] [Finite σ]
variable (P : SubmersivePresentation A B ι σ)

attribute [local instance] Fintype.ofFinite

/-- The finite family of coefficients occurring in the original defining relations. -/
def coefficients : Finset A := by
  classical
  exact Finset.univ.biUnion fun j : σ ↦ (P.relation j).coeffs

/-- The polynomial coefficient ring retains the original base ring. -/
abbrev CoefficientRing := MvPolynomial (coefficients P) R

/-- A coefficient variable is evaluated at the original specified coefficient. -/
def coefficientMap : CoefficientRing R P →ₐ[R] A :=
  MvPolynomial.aeval Subtype.val

local instance coefficientAlgebra : Algebra (CoefficientRing R P) A :=
  (coefficientMap R P).toAlgebra

local instance coefficientTower : IsScalarTower R (CoefficientRing R P) A :=
  IsScalarTower.of_algebraMap_eq' (coefficientMap R P).comp_algebraMap.symm

local instance originalAlgebra : Algebra (CoefficientRing R P) B :=
  ((algebraMap A B).comp (coefficientMap R P).toRingHom).toAlgebra

local instance originalTower : IsScalarTower (CoefficientRing R P) A B :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance originalBaseTower : IsScalarTower R (CoefficientRing R P) B :=
  IsScalarTower.of_algebraMap_eq' (by
    ext r
    change algebraMap R B r =
      algebraMap A B (coefficientMap R P (algebraMap R (CoefficientRing R P) r))
    rw [(coefficientMap R P).commutes]
    exact IsScalarTower.algebraMap_apply R A B r)

/-- Lift a collected coefficient to its displayed polynomial variable. -/
def liftCoefficient (a : A) : CoefficientRing R P := by
  classical
  exact if h : a ∈ coefficients P then MvPolynomial.X ⟨a, h⟩ else 0

/-- Lift a polynomial term by term; no surjectivity of the coefficient map is assumed. -/
def liftPolynomial (p : MvPolynomial ι A) : MvPolynomial ι (CoefficientRing R P) :=
  (AddMonoidAlgebra.coeff p).sum fun m a ↦ MvPolynomial.monomial m (liftCoefficient R P a)

/-- Coefficient evaluation recovers a polynomial supported on the collected coefficients. -/
theorem liftPolynomial_map (p : MvPolynomial ι A) (hp : p.coeffs ⊆ coefficients P) :
    MvPolynomial.map (algebraMap (CoefficientRing R P) A) (liftPolynomial R P p) = p := by
  sorry

/-- The actual finite relation family over the polynomial coefficient ring. -/
def relation (j : σ) : MvPolynomial ι (CoefficientRing R P) :=
  liftPolynomial R P (P.relation j)

/-- The relation family evaluates to the original relations. -/
theorem relation_map (j : σ) :
    MvPolynomial.map (algebraMap (CoefficientRing R P) A) (relation R P j) =
      P.relation j := by
  sorry

/-- Quotient by the specified lifted relation family. -/
abbrev RelationQuotient :=
  MvPolynomial ι (CoefficientRing R P) ⧸ Ideal.span (Set.range (relation R P))

/-- The naive presentation retains the original injection of relations into variables. -/
def prePresentation :
    PreSubmersivePresentation (CoefficientRing R P) (RelationQuotient R P) ι σ :=
  PreSubmersivePresentation.naive (v := relation R P) P.map P.map_inj

/-- The actual coefficient model inverts the displayed Jacobian. -/
abbrev Model := Localization.Away (prePresentation R P).jacobian

/-- The image of an original presentation variable in the model. -/
def generator (j : ι) : Model R P :=
  algebraMap (RelationQuotient R P) (Model R P)
    (Ideal.Quotient.mk _ (MvPolynomial.X j))

/-- Its submersive presentation is the naive quotient followed by one localization. -/
def presentation :
    SubmersivePresentation (CoefficientRing R P) (Model R P) (Unit ⊕ ι) (Unit ⊕ σ) where
  __ := (PreSubmersivePresentation.localizationAway
    (Model R P) (prePresentation R P).jacobian).comp (prePresentation R P)
  jacobian_isUnit := by
    rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.smul_def]
    exact (IsLocalization.Away.algebraMap_isUnit
        (S := Model R P) (prePresentation R P).jacobian).mul
      (SubmersivePresentation.localizationAway
        (Model R P) (prePresentation R P).jacobian).jacobian_isUnit

omit [Algebra R A] [Algebra R B] [IsScalarTower R A B] in
/-- Localization adds one generator and one relation, preserving the relative dimension. -/
theorem presentation_dimension : (presentation R P).dimension = P.dimension := by
  change Nat.card (Unit ⊕ ι) - Nat.card (Unit ⊕ σ) = Nat.card ι - Nat.card σ
  simp [Nat.add_sub_add_left]

omit [Algebra R A] [Algebra R B] [IsScalarTower R A B] in
/-- Dimension zero supplies genuine native étaleness and its finite presentation. -/
theorem etale (hP : P.dimension = 0) : Etale (CoefficientRing R P) (Model R P) := by
  letI := (presentation R P).isStandardSmoothOfRelativeDimension
    ((presentation_dimension R P).trans hP)
  infer_instance

/-- Evaluate the actual quotient at the original presentation generators. -/
def quotientToOriginal : RelationQuotient R P →ₐ[CoefficientRing R P] B :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval P.val) (by sorry)

/-- Evaluation sends the lifted Jacobian to the unit supplied by the original presentation. -/
theorem quotientToOriginal_jacobian :
    quotientToOriginal R P (prePresentation R P).jacobian = P.jacobian := by
  sorry

/-- The map from the localized coefficient model uses the original Jacobian unit. -/
def toOriginal : Model R P →ₐ[CoefficientRing R P] B :=
  IsLocalization.Away.liftAlgHom (prePresentation R P).jacobian
    (f := quotientToOriginal R P)
    ((quotientToOriginal_jacobian R P).symm ▸ P.jacobian_isUnit)

/-- The forward base-change map evaluates coefficients and model generators. -/
def reductionToOriginal : A ⊗[CoefficientRing R P] Model R P →ₐ[A] B :=
  Algebra.TensorProduct.lift (Algebra.ofId A B) (toOriginal R P) (fun _ _ ↦ .all _ _)

/-- Original quotient classes evaluate at the specified tensor-product generators. -/
def originalQuotientToReduction :
    P.Quotient →ₐ[A] A ⊗[CoefficientRing R P] Model R P :=
  Ideal.Quotient.liftₐ P.ker
    (MvPolynomial.aeval fun j ↦ 1 ⊗ₜ[CoefficientRing R P] generator R P j) (by sorry)

/-- The reverse map uses the actual polynomial representatives in the original presentation. -/
def originalToReduction : B →ₐ[A] A ⊗[CoefficientRing R P] Model R P :=
  (originalQuotientToReduction R P).comp
    (P.quotientEquiv.symm.restrictScalars A).toAlgHom

/-- Both directions of the coefficient-model base-change comparison are specified maps. -/
def baseChangeEquiv : A ⊗[CoefficientRing R P] Model R P ≃ₐ[A] B :=
  AlgEquiv.ofAlgHom (reductionToOriginal R P) (originalToReduction R P) (by sorry) (by sorry)

end Algebra.SubmersivePresentation.CoefficientModel

namespace RingHom.FinitePresentation.EtaleSourceDescent

private theorem mem_range_comap_baseChange
    {T S D : Type*} [CommRing T] [CommRing S] [CommRing D]
    [Algebra T S] [Algebra T D] (p : PrimeSpectrum S)
    (hp : PrimeSpectrum.comap (algebraMap T S) p ∈
      Set.range (PrimeSpectrum.comap (algebraMap T D))) :
    p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (S ⊗[T] D))) := by
  let r := PrimeSpectrum.comap (algebraMap T S) p
  let e := Ideal.ResidueField.mapₐ r.asIdeal p.asIdeal (Algebra.ofId T S) rfl
  letI : Algebra r.asIdeal.ResidueField p.asIdeal.ResidueField := e.toAlgebra
  letI : IsScalarTower T r.asIdeal.ResidueField p.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq' e.comp_algebraMap.symm
  letI : Nontrivial (r.asIdeal.ResidueField ⊗[T] D) :=
    (PrimeSpectrum.nontrivial_iff_mem_rangeComap r).mpr hp
  letI : Module.FaithfullyFlat r.asIdeal.ResidueField p.asIdeal.ResidueField := inferInstance
  letI : Nontrivial
      (p.asIdeal.ResidueField ⊗[r.asIdeal.ResidueField] (r.asIdeal.ResidueField ⊗[T] D)) :=
    inferInstance
  let e₁ := Algebra.TensorProduct.cancelBaseChange T r.asIdeal.ResidueField
    p.asIdeal.ResidueField p.asIdeal.ResidueField D
  letI : Nontrivial (p.asIdeal.ResidueField ⊗[T] D) := e₁.symm.toEquiv.nontrivial
  let e₂ := Algebra.TensorProduct.cancelBaseChange T S
    p.asIdeal.ResidueField p.asIdeal.ResidueField D
  letI : Nontrivial (p.asIdeal.ResidueField ⊗[S] (S ⊗[T] D)) := e₂.toEquiv.nontrivial
  exact (PrimeSpectrum.nontrivial_iff_mem_rangeComap p).mp inferInstance

private abbrev GoodElement (T D : Type*) [CommRing T] [CommRing D] [Algebra T D] :=
  {t : T // (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum T)) ⊆
    Set.range (PrimeSpectrum.comap (algebraMap T D))}

private theorem goodElement_span
    {T A B D : Type*} [CommRing T] [CommRing A] [CommRing B] [CommRing D]
    [Algebra T A] [Algebra A B] [Algebra T B] [Algebra T D]
    [IsScalarTower T A B] [Module.FaithfullyFlat A B] [Algebra.Etale T D]
    (φ : D →ₐ[T] B) :
    Ideal.span (Set.range fun t : GoodElement T D ↦ algebraMap T A t.val) = ⊤ := by
  classical
  have hO : IsOpen (Set.range (PrimeSpectrum.comap (algebraMap T D))) :=
    PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation.isOpen_range
  have good (p : PrimeSpectrum A) :
      ∃ t : GoodElement T D, algebraMap T A t.val ∉ p.asIdeal := by
    obtain ⟨q, hq⟩ := (PrimeSpectrum.comap_surjective_of_faithfullyFlat :
      Function.Surjective (PrimeSpectrum.comap (algebraMap A B))) p
    have hmaps : φ.toRingHom.comp (algebraMap T D) =
        (algebraMap A B).comp (algebraMap T A) :=
      φ.comp_algebraMap.trans (IsScalarTower.algebraMap_eq T A B)
    have hr : PrimeSpectrum.comap (algebraMap T A) p ∈
        Set.range (PrimeSpectrum.comap (algebraMap T D)) := by
      refine ⟨PrimeSpectrum.comap φ.toRingHom q, ?_⟩
      rw [← PrimeSpectrum.comap_comp_apply, hmaps, PrimeSpectrum.comap_comp_apply, hq]
    obtain ⟨_, ⟨t, rfl⟩, hmem, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hO _ hr
    exact ⟨⟨t, hsub⟩, hmem⟩
  by_contra h
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
  obtain ⟨t, ht⟩ := good ⟨m, hm.isPrime⟩
  exact ht (hle (Ideal.subset_span ⟨t, rfl⟩))

private theorem unitCoefficients_exists
    {T A B D : Type*} [CommRing T] [CommRing A] [CommRing B] [CommRing D]
    [Algebra T A] [Algebra A B] [Algebra T B] [Algebra T D]
    [IsScalarTower T A B] [Module.FaithfullyFlat A B] [Algebra.Etale T D]
    (φ : D →ₐ[T] B) :
    ∃ c : GoodElement T D →₀ A,
      c.sum (fun t a ↦ a * algebraMap T A t.val) = 1 := by
  have h1 : (1 : A) ∈
      Ideal.span (Set.range fun t : GoodElement T D ↦ algebraMap T A t.val) := by
    rw [goodElement_span φ]
    trivial
  simpa only [smul_eq_mul] using Finsupp.mem_span_range_iff_exists_finsupp.mp h1

section UnitRelation

variable {T A B D : Type*} [CommRing T] [CommRing A] [CommRing B] [CommRing D]
variable [Algebra T A] [Algebra A B] [Algebra T B] [Algebra T D]
variable [IsScalarTower T A B] [Module.FaithfullyFlat A B] [Algebra.Etale T D]
variable (φ : D →ₐ[T] B)

private def unitCoefficients : GoodElement T D →₀ A :=
  (unitCoefficients_exists (A := A) φ).choose

private theorem unitCoefficients_spec :
    (unitCoefficients (A := A) φ).sum
      (fun t a ↦ a * algebraMap T A t.val) = 1 :=
  (unitCoefficients_exists (A := A) φ).choose_spec

private abbrev UnitIndex := (unitCoefficients (A := A) φ).support

private abbrev UnitPolynomial := MvPolynomial (UnitIndex (A := A) φ) T

private def unitRelation : UnitPolynomial (A := A) φ :=
  (∑ j : UnitIndex (A := A) φ,
    MvPolynomial.C j.val.val * MvPolynomial.X j) - 1

private abbrev UnitRelationRing := UnitPolynomial (A := A) φ ⧸ Ideal.span {unitRelation (A := A) φ}

private def unitQuotient : UnitPolynomial (A := A) φ →ₐ[T] UnitRelationRing (A := A) φ :=
  Ideal.Quotient.mkₐ T _

private def unitGenerator (j : UnitIndex (A := A) φ) : UnitRelationRing (A := A) φ :=
  unitQuotient (A := A) φ (MvPolynomial.X j)

private def unitPolynomialToBase : UnitPolynomial (A := A) φ →ₐ[T] A :=
  MvPolynomial.aeval fun j ↦ unitCoefficients (A := A) φ j.val

private theorem unitPolynomialToBase_relation :
    unitPolynomialToBase (A := A) φ (unitRelation (A := A) φ) = 0 := by
  classical
  have h := unitCoefficients_spec (A := A) φ
  have hs : (∑ j : UnitIndex (A := A) φ,
      algebraMap T A j.val.val * unitCoefficients (A := A) φ j.val) = 1 := by
    rw [Finset.sum_coe_sort (unitCoefficients (A := A) φ).support
      (fun t : GoodElement T D ↦ algebraMap T A t.val * unitCoefficients (A := A) φ t)]
    simpa only [Finsupp.sum, mul_comm] using h
  simpa only [unitPolynomialToBase, unitRelation, map_sub, map_sum, map_mul,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X, map_one] using sub_eq_zero.mpr hs

private def unitToBase : UnitRelationRing (A := A) φ →ₐ[T] A :=
  Ideal.Quotient.liftₐ _ (unitPolynomialToBase (A := A) φ) (by
    change Ideal.span {unitRelation (A := A) φ} ≤
      RingHom.ker (unitPolynomialToBase (A := A) φ).toRingHom
    rw [Ideal.span_le]
    rintro _ rfl
    exact unitPolynomialToBase_relation (A := A) φ)

private theorem unitRing_finitePresentation :
    Algebra.FinitePresentation T (UnitRelationRing (A := A) φ) :=
  Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)

private theorem unitRelation_eq :
    (∑ j : UnitIndex (A := A) φ,
      algebraMap T (UnitRelationRing (A := A) φ) j.val.val *
        unitGenerator (A := A) φ j) = 1 := by
  have h0 : unitQuotient (A := A) φ (unitRelation (A := A) φ) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  simpa [unitRelation, unitGenerator, map_sub, map_sum, map_mul, sub_eq_zero] using h0

private theorem unitBaseChange_faithfullyFlat :
    Module.FaithfullyFlat (UnitRelationRing (A := A) φ)
      (UnitRelationRing (A := A) φ ⊗[T] D) := by
  classical
  apply Module.FaithfullyFlat.of_comap_surjective
  intro p
  have hex : ∃ j : UnitIndex (A := A) φ,
      algebraMap T (UnitRelationRing (A := A) φ) j.val.val ∉ p.asIdeal := by
    by_contra h
    have hmem : ∀ j : UnitIndex (A := A) φ,
        algebraMap T (UnitRelationRing (A := A) φ) j.val.val ∈ p.asIdeal := by
      simpa using h
    have hsum : (∑ j : UnitIndex (A := A) φ,
        algebraMap T (UnitRelationRing (A := A) φ) j.val.val *
          unitGenerator (A := A) φ j) ∈ p.asIdeal :=
      p.asIdeal.sum_mem fun j _ ↦ p.asIdeal.mul_mem_right _ (hmem j)
    rw [unitRelation_eq] at hsum
    exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hsum)
  obtain ⟨j, hj⟩ := hex
  apply mem_range_comap_baseChange p
  exact j.val.property hj

end UnitRelation

private theorem finitePresentation_of_faithfulTensor
    {R T A B D : Type*} [CommRing R] [CommRing T] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R T] [Algebra R A] [Algebra R B] [Algebra R D]
    [Algebra T A] [Algebra T D] [Algebra A B]
    [IsScalarTower R T A] [IsScalarTower R T D] [IsScalarTower R A B]
    [Algebra.FinitePresentation R T] [Algebra.FinitePresentation R D]
    [Algebra.FinitePresentation R B] [Module.FaithfullyFlat T D]
    (e : A ⊗[T] D ≃ₐ[A] B) : Algebra.FinitePresentation R A := by
  let γ : D →ₐ[R] B :=
    (e.toAlgHom.restrictScalars R).comp
      ((Algebra.TensorProduct.includeRight (R := T) (A := A) (B := D)).restrictScalars R)
  letI : Algebra D B := γ.toAlgebra
  letI : IsScalarTower R D B := IsScalarTower.of_algebraMap_eq' γ.comp_algebraMap.symm
  let eD : D ⊗[T] A ≃ₐ[D] B :=
    AlgEquiv.ofRingEquiv
      (f := (Algebra.TensorProduct.comm T D A).toRingEquiv.trans e.toRingEquiv)
      (by intro d; rfl)
  letI : Algebra.FinitePresentation D B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R D B
  letI : Algebra.FinitePresentation D (D ⊗[T] A) :=
    Algebra.FinitePresentation.equiv eD.symm
  letI : Algebra.FinitePresentation T A :=
    Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat D
  exact Algebra.FinitePresentation.trans R T A

private theorem algebraFinitePresentation
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FinitePresentation R B] [Module.FaithfullyFlat A B] [Algebra.Etale A B] :
    Algebra.FinitePresentation R A := by
  classical
  let h := (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero
    (R := A) (S := B)).mp inferInstance
  obtain ⟨ι, σ, hσ, hι, P, hP⟩ := h.out
  letI := hσ
  letI := hι
  let T := Algebra.SubmersivePresentation.CoefficientModel.CoefficientRing R P
  let D := Algebra.SubmersivePresentation.CoefficientModel.Model R P
  letI : Algebra T A :=
    Algebra.SubmersivePresentation.CoefficientModel.coefficientAlgebra R P
  letI : IsScalarTower R T A :=
    Algebra.SubmersivePresentation.CoefficientModel.coefficientTower R P
  letI : Algebra T B :=
    Algebra.SubmersivePresentation.CoefficientModel.originalAlgebra R P
  letI : IsScalarTower T A B :=
    Algebra.SubmersivePresentation.CoefficientModel.originalTower R P
  letI : IsScalarTower R T B :=
    Algebra.SubmersivePresentation.CoefficientModel.originalBaseTower R P
  letI : Algebra.Etale T D :=
    Algebra.SubmersivePresentation.CoefficientModel.etale R P hP
  let φ : D →ₐ[T] B := Algebra.SubmersivePresentation.CoefficientModel.toOriginal R P
  let T' := UnitRelationRing (A := A) φ
  let a : T' →ₐ[T] A := unitToBase (A := A) φ
  letI : Algebra T' A := a.toAlgebra
  letI : IsScalarTower T T' A := IsScalarTower.of_algebraMap_eq' a.comp_algebraMap.symm
  letI : Algebra R T' := inferInstance
  letI : IsScalarTower R T T' := inferInstance
  letI : IsScalarTower R T' A :=
    IsScalarTower.of_algebraMap_eq' (a.restrictScalars R).comp_algebraMap.symm
  let D' := T' ⊗[T] D
  let eA : A ⊗[T'] D' ≃ₐ[A] B :=
    (Algebra.TensorProduct.cancelBaseChange T T' A A D).trans
      (Algebra.SubmersivePresentation.CoefficientModel.baseChangeEquiv R P)
  letI : Algebra.FinitePresentation R T := inferInstance
  letI : Algebra.FinitePresentation T T' := unitRing_finitePresentation (A := A) φ
  letI : Algebra.FinitePresentation R T' := Algebra.FinitePresentation.trans R T T'
  letI : Algebra.FinitePresentation T' D' := inferInstance
  letI : Algebra.FinitePresentation R D' := Algebra.FinitePresentation.trans R T' D'
  letI : Module.FaithfullyFlat T' D' := unitBaseChange_faithfullyFlat (A := A) φ
  exact finitePresentation_of_faithfulTensor (R := R) eA

end RingHom.FinitePresentation.EtaleSourceDescent

namespace RingHom.FinitePresentation

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable {f : R →+* A} {g : A →+* B}

/-- Finite presentation descends from a composite along a faithfully flat étale second map.
The finite coefficient model and its faithful refinement are actual polynomial quotients and
Jacobian localizations; finite presentations descend through their explicit tensor square. -/
theorem of_comp_of_faithfullyFlat_of_etale
    (hcomp : (g.comp f).FinitePresentation) (hfaithfullyFlat : g.FaithfullyFlat)
    (hetale : g.Etale) : f.FinitePresentation := by
  algebraize [f, g, g.comp f]
  exact EtaleSourceDescent.algebraFinitePresentation (R := R) (A := A) (B := B)

end RingHom.FinitePresentation
