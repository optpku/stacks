/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Polynomial.Quotient
public import ReasLib.RingTheory.Topology.Adic.Basic
public import ReasLib.RingTheory.Topology.Adic.Complete
public import stacks_project.Chap87.Remark_87_28_2_RestrictedPowerSeries
public import stacks_project.Chap88.«88_3_0_1_NaiveCotangent»
public import stacks_project.Chap88.Remark_88_11_2_Presentation

/-!
# Comparison of restricted and I-adic completed naive cotangent complexes

When `A` is adic and `I` is an ideal of definition, `A{x_ι}` is identified with
the `I`-adic polynomial completion `A[x_ι]^∧` of 88.3.0.1, and a restricted
presentation induces an `I`-adic presentation with isomorphic Jacobian complexes.
-/

@[expose] public section

open Algebra.Extension
open Algebra.NaiveCotangent
open CategoryTheory
open RestrictedPowerSeries
open TopologicalRing
open TopologicalRing.Ideal
open Algebra.NaiveCotangent.Adic (polynomialIdeal polynomialCompletion)

noncomputable section

universe u

namespace Algebra.NaiveCotangent.Restricted

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A]

/-- An open ideal is a neighborhood of zero. -/
theorem isOpen_mem_nhds_zero (J : OpenIdeal A) : (J.1 : Set A) ∈ nhds (0 : A) :=
  J.2.mem_nhds J.1.zero_mem

variable (ι : Type u) (I : Ideal A)

/-- A power of an ideal of definition contained in a given open ideal. -/
def powIndex (hI : IsIdealOfDefinition I) (J : OpenIdeal A) : ℕ :=
  Classical.choose (hI.2 (J.1 : Set A) (isOpen_mem_nhds_zero J))

/-- The chosen power of `I` is contained in the given open ideal. -/
theorem powIndex_le (hI : IsIdealOfDefinition I) (J : OpenIdeal A) :
    I ^ powIndex I hI J ≤ J.1 :=
  fun _ hx ↦ Classical.choose_spec (hI.2 (J.1 : Set A) (isOpen_mem_nhds_zero J)) hx

/-- Powers of an adic ideal remain open. -/
theorem isOpen_pow (hI : IsAdic I) (n : ℕ) :
    IsOpen ((I ^ n : Ideal A) : Set A) := sorry

/-- Named identification of the 88.3.0.1 polynomial completion with the `I`-adic
restricted power series ring, via the extended coefficient ideals. -/
def polynomialCompletion_eq :
    polynomialCompletion A I ι = IAdicRestrictedPowerSeries ι I :=
  congrArg (fun J : Ideal (MvPolynomial ι A) ↦ AdicCompletion J (MvPolynomial ι A))
    (rfl : polynomialIdeal A I ι = I.map (algebraMap A (MvPolynomial ι A)))

/-- The 88.3.0.1 polynomial completion agrees with the `I`-adic restricted
power series ring after identifying the extended coefficient ideals. -/
theorem polynomialCompletion_eq_spec :
    polynomialCompletion A I ι = IAdicRestrictedPowerSeries ι I :=
  sorry

/-- Transport from the 88.3.0.1 polynomial completion to `IAdicRestrictedPowerSeries`
along `polynomialCompletion_eq`. -/
def toIAdicRestrictedPowerSeries (F : polynomialCompletion A I ι) :
    IAdicRestrictedPowerSeries ι I :=
  Eq.mp (polynomialCompletion_eq ι I) F

/-- `toIAdicRestrictedPowerSeries` is transport along `polynomialCompletion_eq`. -/
theorem toIAdicRestrictedPowerSeries_eq (F : polynomialCompletion A I ι) :
    toIAdicRestrictedPowerSeries ι I F = Eq.mp (polynomialCompletion_eq ι I) F :=
  sorry

/-- Transport from `IAdicRestrictedPowerSeries` to the 88.3.0.1 polynomial
completion along `polynomialCompletion_eq`. -/
def ofIAdicRestrictedPowerSeries (F : IAdicRestrictedPowerSeries ι I) :
    polynomialCompletion A I ι :=
  Eq.mpr (polynomialCompletion_eq ι I) F

/-- `ofIAdicRestrictedPowerSeries` is transport along `polynomialCompletion_eq`. -/
theorem ofIAdicRestrictedPowerSeries_eq (F : IAdicRestrictedPowerSeries ι I) :
    ofIAdicRestrictedPowerSeries ι I F = Eq.mpr (polynomialCompletion_eq ι I) F :=
  sorry

variable [IsAdicRing A]

/-- In an adic ring, powers of an ideal of definition remain open. -/
theorem isOpen_pow_of_idealOfDefinition (hI : IsIdealOfDefinition I) (n : ℕ) :
    IsOpen ((I ^ n : Ideal A) : Set A) := sorry

/-- The open ideal `I ^ n` attached to an ideal of definition of an adic ring. -/
def openPow (hI : IsIdealOfDefinition I) (n : ℕ) : OpenIdeal A :=
  ⟨I ^ n, isOpen_pow_of_idealOfDefinition I hI n⟩

/-- The underlying ideal of `openPow` is `I ^ n`. -/
theorem openPow_val (hI : IsIdealOfDefinition I) (n : ℕ) :
    (openPow I hI n).1 = I ^ n := sorry

/-- Component evaluation of restricted power series, as an `A`-algebra map. -/
def componentAlgHom (J : OpenIdeal A) :
    RestrictedPowerSeries ι A →ₐ[A] MvPolynomial ι (A ⧸ J.1) where
  __ := component J
  commutes' := sorry

/-- `componentAlgHom` is the component evaluation map. -/
theorem componentAlgHom_apply (J : OpenIdeal A) (f : RestrictedPowerSeries ι A) :
    componentAlgHom ι J f = component J f := sorry

/-- The polynomial identification `(A ⧸ I^n)[x_ι] ≃ₐ[A] A[x_ι] ⧸ (I^n · A[x_ι])`. -/
def stageQuotientEquiv (n : ℕ) :
    MvPolynomial ι (A ⧸ I ^ n) ≃ₐ[A]
      MvPolynomial ι A ⧸ (I ^ n).map (algebraMap A (MvPolynomial ι A)) :=
  MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ n)

/-- `stageQuotientEquiv` is the polynomial quotient identification. -/
theorem stageQuotientEquiv_eq (n : ℕ) :
    stageQuotientEquiv ι I n =
      MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ n) := sorry

/-- The extended ideal of 88.3.0.1 is the image of `I` in `A[x_ι]`. -/
theorem polynomialIdeal_eq_map :
    polynomialIdeal A I ι = I.map (algebraMap A (MvPolynomial ι A)) :=
  sorry

/-- Extending the coefficient ideal commutes with taking powers. -/
theorem polynomialIdeal_pow (n : ℕ) :
    (I ^ n).map (algebraMap A (MvPolynomial ι A)) = polynomialIdeal A I ι ^ n :=
  sorry

/-- Finite-stage map from `A{x_ι}` to `A[x_ι] / (I · A[x_ι])^n`. -/
def toAdicStage (hI : IsIdealOfDefinition I) (n : ℕ) :
    RestrictedPowerSeries ι A →ₐ[A]
      MvPolynomial ι A ⧸ (I.map (algebraMap A (MvPolynomial ι A))) ^ n :=
  (Ideal.quotientEquivAlgOfEq A
      (Ideal.map_pow (algebraMap A (MvPolynomial ι A)) I n)).toAlgHom.comp
    ((stageQuotientEquiv ι I n).toAlgHom.comp (componentAlgHom ι (openPow I hI n)))

/-- Finite-stage maps `toAdicStage` are compatible with adic transition maps. -/
theorem toAdicStage_compatible (hI : IsIdealOfDefinition I) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hle)).comp
      (toAdicStage ι I hI n) =
      toAdicStage ι I hI m := sorry

/-- The `A`-algebra map `A{x_ι} → A[x_ι]^∧` induced by the inverse-system
identification of Remark 87.28.2, landing in `IAdicRestrictedPowerSeries`. -/
def toIAdicAlgHom (hI : IsIdealOfDefinition I) :
    RestrictedPowerSeries ι A →ₐ[A] IAdicRestrictedPowerSeries ι I :=
  AdicCompletion.liftAlgHom (I.map (algebraMap A (MvPolynomial ι A)))
    (toAdicStage ι I hI) (toAdicStage_compatible ι I hI)

/-- The `A`-algebra map `A{x_ι} → A[x_ι]^∧` induced by the inverse-system
identification of Remark 87.28.2. -/
def toAdicAlgHom (hI : IsIdealOfDefinition I) :
    RestrictedPowerSeries ι A →ₐ[A] polynomialCompletion A I ι where
  toFun f := ofIAdicRestrictedPowerSeries ι I (toIAdicAlgHom ι I hI f)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

/-- Evaluating `toIAdicAlgHom` at a finite adic stage recovers `toAdicStage`. -/
theorem eval_toIAdicAlgHom (hI : IsIdealOfDefinition I) (n : ℕ)
    (f : RestrictedPowerSeries ι A) :
    AdicCompletion.evalₐ (I.map (algebraMap A (MvPolynomial ι A))) n
        (toIAdicAlgHom ι I hI f) =
      toAdicStage ι I hI n f := sorry

/-- `toAdicAlgHom` is `toIAdicAlgHom` transported along `polynomialCompletion_eq`. -/
theorem toAdicAlgHom_eq (hI : IsIdealOfDefinition I)
    (f : RestrictedPowerSeries ι A) :
    toAdicAlgHom ι I hI f =
      ofIAdicRestrictedPowerSeries ι I (toIAdicAlgHom ι I hI f) := sorry

/-- Compatibility of the inverse-system family used to send a polynomial
completion back to restricted power series. -/
theorem ofAdic_compatible (hI : IsIdealOfDefinition I)
    (F : polynomialCompletion A I ι) :
    Compatible fun J : OpenIdeal A ↦
      MvPolynomial.map (Ideal.Quotient.factor (powIndex_le I hI J))
        (IAdicRestrictedPowerSeries.stageHom ι I (powIndex I hI J)
          (toIAdicRestrictedPowerSeries ι I F)) := sorry

/-- The underlying map `A[x_ι]^∧ → A{x_ι}` of the identification in
Remark 87.28.2. -/
def ofAdic (hI : IsIdealOfDefinition I) (F : polynomialCompletion A I ι) :
    RestrictedPowerSeries ι A :=
  ⟨fun J ↦
    MvPolynomial.map (Ideal.Quotient.factor (powIndex_le I hI J))
      (IAdicRestrictedPowerSeries.stageHom ι I (powIndex I hI J)
        (toIAdicRestrictedPowerSeries ι I F)),
    ofAdic_compatible ι I hI F⟩

/-- Components of `ofAdic` are the polynomial stages mapped to the open ideal. -/
theorem ofAdic_component (hI : IsIdealOfDefinition I)
    (F : polynomialCompletion A I ι) (J : OpenIdeal A) :
    component J (ofAdic ι I hI F) =
      MvPolynomial.map (Ideal.Quotient.factor (powIndex_le I hI J))
        (IAdicRestrictedPowerSeries.stageHom ι I (powIndex I hI J)
          (toIAdicRestrictedPowerSeries ι I F)) := sorry

/-- The `A`-algebra map `A[x_ι]^∧ → A{x_ι}` induced by the inverse-system
identification of Remark 87.28.2. -/
def ofAdicAlgHom (hI : IsIdealOfDefinition I) :
    polynomialCompletion A I ι →ₐ[A] RestrictedPowerSeries ι A where
  toFun := ofAdic ι I hI
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

/-- `ofAdicAlgHom` is `ofAdic` on the underlying function. -/
theorem ofAdicAlgHom_apply (hI : IsIdealOfDefinition I)
    (F : polynomialCompletion A I ι) :
    ofAdicAlgHom ι I hI F = ofAdic ι I hI F := sorry

/-- The `A`-algebra identification `A{x_ι} ≃ₐ[A] A[x_ι]^∧` of Formal Spaces,
Remark 87.28.2, when `I` is an ideal of definition. -/
def adicEquiv (hI : IsIdealOfDefinition I) :
    RestrictedPowerSeries ι A ≃ₐ[A] polynomialCompletion A I ι :=
  AlgEquiv.ofAlgHom (toAdicAlgHom ι I hI) (ofAdicAlgHom ι I hI) sorry sorry

/-- The identification sends restricted polynomials to completed polynomials. -/
theorem adicEquiv_ofPolynomial (hI : IsIdealOfDefinition I) (g : MvPolynomial ι A) :
    adicEquiv ι I hI (ofPolynomial g) =
      AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) g := sorry

/-- The identification sends variables `x_i` to the completed variables. -/
theorem adicEquiv_X (hI : IsIdealOfDefinition I) (i : ι) :
    adicEquiv ι I hI (ofPolynomial (MvPolynomial.X i)) =
      AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) (MvPolynomial.X i) :=
  sorry

variable {B : Type u} [CommRing B] [Algebra A B]

namespace Presentation

/-- The `I`-adic completed polynomial presentation associated with a restricted
presentation along the identification of Remark 87.28.2. -/
def toAdic (hI : IsIdealOfDefinition I) (P : Presentation A B ι) :
    Algebra.NaiveCotangent.Adic.Presentation A B I ι :=
  Algebra.NaiveCotangent.Adic.Presentation.ofSurjective
    (P.toAlgHom.comp (adicEquiv ι I hI).symm.toAlgHom)
    (P.surjective.comp (adicEquiv ι I hI).symm.surjective)

/-- The structure map of `toAdic` is the restricted structure map composed with
the inverse identification. -/
theorem toAdic_toAlgHom (hI : IsIdealOfDefinition I) (P : Presentation A B ι) :
    (toAdic ι I hI P).toAlgHom = P.toAlgHom.comp (adicEquiv ι I hI).symm.toAlgHom :=
  sorry

/-- Compatibility of `adicEquiv` with the two structure maps to `B`. -/
theorem toAdicExtensionHom_commutes (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) :
    (IsScalarTower.toAlgHom A (toAdic ι I hI P).toExtension.Ring B).comp
        (adicEquiv ι I hI).toAlgHom =
      (IsScalarTower.toAlgHom A B B).comp
        (IsScalarTower.toAlgHom A P.toExtension.Ring B) :=
  sorry

/-- The morphism of extensions induced by `adicEquiv`. -/
def toAdicExtensionHom (hI : IsIdealOfDefinition I) (P : Presentation A B ι) :
    P.toExtension.Hom (toAdic ι I hI P).toExtension :=
  Extension.Hom.ofAlgHom (adicEquiv ι I hI).toAlgHom
    (toAdicExtensionHom_commutes ι I hI P)

/-- Compatibility of `adicEquiv.symm` with the two structure maps to `B`. -/
theorem ofAdicExtensionHom_commutes (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) :
    (IsScalarTower.toAlgHom A P.toExtension.Ring B).comp
        (adicEquiv ι I hI).symm.toAlgHom =
      (IsScalarTower.toAlgHom A B B).comp
        (IsScalarTower.toAlgHom A (toAdic ι I hI P).toExtension.Ring B) :=
  sorry

/-- The morphism of extensions induced by `adicEquiv.symm`. -/
def ofAdicExtensionHom (hI : IsIdealOfDefinition I) (P : Presentation A B ι) :
    (toAdic ι I hI P).toExtension.Hom P.toExtension :=
  Extension.Hom.ofAlgHom (adicEquiv ι I hI).symm.toAlgHom
    (ofAdicExtensionHom_commutes ι I hI P)

/-- Inverse laws for the conormal maps induced by `adicEquiv`. -/
theorem cotangentIso_toAdic_comp (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) :
    (Cotangent.map (toAdicExtensionHom ι I hI P)).comp
        (Cotangent.map (ofAdicExtensionHom ι I hI P)) =
      LinearMap.id :=
  sorry

/-- Inverse laws for the conormal maps induced by `adicEquiv.symm`. -/
theorem cotangentIso_ofAdic_comp (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) :
    (Cotangent.map (ofAdicExtensionHom ι I hI P)).comp
        (Cotangent.map (toAdicExtensionHom ι I hI P)) =
      LinearMap.id :=
  sorry

/-- The canonical identification of conormal modules along `adicEquiv`. -/
def cotangentIso_toAdic (hI : IsIdealOfDefinition I) (P : Presentation A B ι) :
    P.toExtension.Cotangent ≃ₗ[B]
      (toAdic ι I hI P).toExtension.Cotangent :=
  LinearEquiv.ofLinear
    (Cotangent.map (toAdicExtensionHom ι I hI P))
    (Cotangent.map (ofAdicExtensionHom ι I hI P))
    (cotangentIso_toAdic_comp ι I hI P)
    (cotangentIso_ofAdic_comp ι I hI P)

end Presentation

variable [Fintype ι]

/-- Higher components of the `I`-adic Jacobian complex of a transported
restricted presentation are the zero object of `ModuleCat`. -/
def adicComponentSuccIsoUnit (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) (n : ℕ) :
    (Adic.complex (Presentation.toAdic ι I hI P)).X (n + 2) ≅
      ModuleCat.of B PUnit :=
  ChainComplex.mk'XIso
    (ModuleCat.of B (ι → B))
    (ModuleCat.of B (Presentation.toAdic ι I hI P).toExtension.Cotangent)
    (ModuleCat.ofHom (Adic.jacobian (Presentation.toAdic ι I hI P)))
    (fun {_ _} _ ↦ ⟨ModuleCat.of B PUnit, 0, CategoryTheory.Limits.zero_comp⟩)
    n

/-- Components of the identification of restricted and `I`-adic Jacobian
complexes along `adicEquiv`. -/
def toAdicIsoComponent (hI : IsIdealOfDefinition I) (P : Presentation A B ι) :
    ∀ n, (complex P).X n ≅ (Adic.complex (Presentation.toAdic ι I hI P)).X n
  | 0 =>
    (componentZeroIso P).trans
      (Adic.componentZeroIso (Presentation.toAdic ι I hI P)).symm
  | 1 =>
    (componentOneIso P).trans (Presentation.cotangentIso_toAdic ι I hI P).toModuleIso
  | n + 2 =>
    (componentSuccIsoUnit P n).trans (adicComponentSuccIsoUnit ι I hI P n).symm

/-- The componentwise identification along `adicEquiv` commutes with
differentials. -/
theorem toAdicIsoComponent_comm (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    (toAdicIsoComponent ι I hI P i).hom ≫
        (Adic.complex (Presentation.toAdic ι I hI P)).d i j =
      (complex P).d i j ≫ (toAdicIsoComponent ι I hI P j).hom :=
  sorry

/-- The restricted Jacobian complex is canonically isomorphic to the `I`-adic
Jacobian complex of the transported presentation, via `adicEquiv`. -/
def complexIso_toAdic (hI : IsIdealOfDefinition I) (P : Presentation A B ι) :
    complex P ≅ Adic.complex (Presentation.toAdic ι I hI P) :=
  HomologicalComplex.Hom.isoOfComponents (toAdicIsoComponent ι I hI P)
    (toAdicIsoComponent_comm ι I hI P)

/-- The degree-zero component of `complexIso_toAdic` is the identity on
`ι → B`. -/
theorem complexIso_toAdic_X_zero (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) :
    (complexIso_toAdic ι I hI P).hom.f 0 =
      (toAdicIsoComponent ι I hI P 0).hom :=
  sorry

/-- The degree-one component of `complexIso_toAdic` is the conormal map of
`adicEquiv`. -/
theorem complexIso_toAdic_X_one (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) :
    (complexIso_toAdic ι I hI P).hom.f 1 =
      (toAdicIsoComponent ι I hI P 1).hom :=
  sorry

/-- The restricted Jacobian complex is homotopy equivalent to the `I`-adic
Jacobian complex of the transported presentation. -/
theorem complex_homotopyEquiv_toAdic (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) :
    Nonempty
      (HomotopyEquiv (complex P)
        (Algebra.NaiveCotangent.Adic.complex (Presentation.toAdic ι I hI P))) :=
  sorry

end Algebra.NaiveCotangent.Restricted
