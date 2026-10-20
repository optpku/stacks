/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.DeRham.Connection.Adic
public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers.PolynomialPoincare
public import Mathlib.Algebra.Homology.QuasiIso

@[expose] public section

open CategoryTheory
open DPPolynomial.DeRham
open exteriorPower.form
open scoped TensorProduct

universe u

namespace DPPolynomial.DeRham

section CompletedForms

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable {J : Ideal B} (δ : DividedPowers J) (ι : Type u) (p : ℕ)

/-- The derivative on completed polynomial forms is the continuous canonical de Rham derivative. -/
noncomputable def completedPolynomialDifferential (degree : ℕ) :
    completedPolynomialForm A B δ ι p degree →+
      completedPolynomialForm A B δ ι p (degree + 1) :=
  AdicCompletion.completeAddMap B B p
    (canonicalFamily A (DPPolynomial B ι) (DPPolynomial.dividedPowers (ι := ι) δ) degree).toAddMonoidHom

/-- Polynomial exterior multiplication, with the coefficient action restricted to `B`. -/
noncomputable def polynomialLeftWedge (degree : ℕ) :
    formB A (DPPolynomial B ι) (DPPolynomial.dividedPowers (ι := ι) δ) →ₗ[B]
      exteriorPower.form (DPPolynomial B ι)
        (formB A (DPPolynomial B ι) (DPPolynomial.dividedPowers (ι := ι) δ)) degree →ₗ[B]
        exteriorPower.form (DPPolynomial B ι)
          (formB A (DPPolynomial B ι) (DPPolynomial.dividedPowers (ι := ι) δ))
          (degree + 1) where
  toFun first :=
    { toFun := wedge (DPPolynomial B ι) 1 degree first
      map_add' := sorry
      map_smul' := sorry }
  map_add' := sorry
  map_smul' := sorry

/-- Wedge by a completed base one-form in the completed polynomial forms. -/
noncomputable def completedPolynomialLeftWedge (degree : ℕ) :
    exteriorPower.completedForm B p (formB A B δ) 1 →ₗ[completedRingB B p]
      completedPolynomialForm A B δ ι p degree →ₗ[completedRingB B p]
        completedPolynomialForm A B δ ι p (degree + 1) :=
  (AdicCompletion.completeBilinear B p (polynomialLeftWedge A B δ ι degree)).comp
    (completedFormComparison A B δ ι p 1)

/-- Completing the base differential preserves its values on algebraic forms. -/
theorem completedBaseDifferential_of (degree : ℕ)
    (form : exteriorPower.form B (formB A B δ) degree) :
    completedBaseDifferential A B δ p degree
        (AdicCompletion.of (principalIdealB B p) _ form) =
      AdicCompletion.of (principalIdealB B p) _ (canonicalFamily A B δ degree form) := sorry

/-- Completing the polynomial differential preserves its values on algebraic forms. -/
theorem completedPolynomialDifferential_of (degree : ℕ)
    (form : exteriorPower.form (DPPolynomial B ι)
      (formB A (DPPolynomial B ι) (DPPolynomial.dividedPowers (ι := ι) δ)) degree) :
    completedPolynomialDifferential A B δ ι p degree
        (AdicCompletion.of (principalIdealB B p) _ form) =
      AdicCompletion.of (principalIdealB B p) _
        (canonicalFamily A (DPPolynomial B ι)
          (DPPolynomial.dividedPowers (ι := ι) δ) degree form) := sorry

/-- The completed base wedge specializes to the canonical exterior wedge. -/
theorem completedBaseLeftWedge_of (degree : ℕ) (first : formB A B δ)
    (second : exteriorPower.form B (formB A B δ) degree) :
    completedBaseLeftWedge A B δ p degree
        (AdicCompletion.of (principalIdealB B p) _ first)
        (AdicCompletion.of (principalIdealB B p) _ second) =
      AdicCompletion.of (principalIdealB B p) _ (wedge B 1 degree first second) := sorry

/-- The restricted polynomial wedge is the canonical polynomial exterior wedge. -/
theorem polynomialLeftWedge_apply (degree : ℕ)
    (first : formB A (DPPolynomial B ι) (DPPolynomial.dividedPowers (ι := ι) δ))
    (second : exteriorPower.form (DPPolynomial B ι)
      (formB A (DPPolynomial B ι) (DPPolynomial.dividedPowers (ι := ι) δ)) degree) :
    polynomialLeftWedge A B δ ι degree first second =
      wedge (DPPolynomial B ι) 1 degree first second := sorry

/-- Wedge by a completed base one-form first applies the completed canonical form map. -/
theorem completedPolynomialLeftWedge_apply (degree : ℕ)
    (first : exteriorPower.completedForm B p (formB A B δ) 1)
    (second : completedPolynomialForm A B δ ι p degree) :
    completedPolynomialLeftWedge A B δ ι p degree first second =
      AdicCompletion.completeBilinear B p (polynomialLeftWedge A B δ ι degree)
        (completedFormComparison A B δ ι p 1 first) second := sorry

/-- Completed form comparison agrees with scalar extension on pure uncompleted forms. -/
theorem completedFormComparison_of (degree : ℕ)
    (form : exteriorPower.form B (formB A B δ) degree) :
    completedFormComparison A B δ ι p degree
        (AdicCompletion.of (principalIdealB B p) _ form) =
      AdicCompletion.of (principalIdealB B p) _
        (Connection.inducedForm (coefficientFormMap A B δ ι) degree form) := sorry

/-- The completed derivation extends the original divided-power derivation. -/
theorem completedDerivation_of (coefficient : B) :
    completedDerivation A B δ p (AdicCompletion.of (principalIdealB B p) B coefficient) =
      AdicCompletion.of (principalIdealB B p) _ (derivationB A B δ coefficient) := sorry

end CompletedForms

section CompletedComparison

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable {J : Ideal B} (δ : DividedPowers J) (ι : Type u) (p : ℕ)
variable {M : Type u} [AddCommGroup M] [Module (completedRingB B p) M]

/-- The induced connection pairing uses only the given completed-valued source connection. -/
noncomputable def adicPolynomialPairing (conn : Connection.Adic A B δ p M) (degree : ℕ) :
    M →+ completedPolynomialForm A B δ ι p degree →+
      completedTensorB (completedRingB B p) p M
        (completedPolynomialForm A B δ ι p (degree + 1)) where
  toFun element :=
    { toFun := fun form ↦
        AdicCompletion.map (principalIdealB (completedRingB B p) p)
          (TensorProduct.map (LinearMap.id : M →ₗ[completedRingB B p] M)
            ((completedPolynomialLeftWedge A B δ ι p degree).flip form))
          (conn.toAddMonoidHom element) +
        AdicCompletion.of (principalIdealB (completedRingB B p) p) _
          (element ⊗ₜ[completedRingB B p]
            completedPolynomialDifferential A B δ ι p degree form)
      map_zero' := sorry
      map_add' := sorry }
  map_zero' := sorry
  map_add' := sorry

/-- The completed scalar-extension differential is the continuous tensor Leibniz extension. -/
noncomputable def adicPolynomialDifferential (conn : Connection.Adic A B δ p M) (degree : ℕ) :
    completedTensorB (completedRingB B p) p M (completedPolynomialForm A B δ ι p degree) →+
      completedTensorB (completedRingB B p) p M
        (completedPolynomialForm A B δ ι p (degree + 1)) :=
  AdicCompletion.extendCompleteAddMap (completedRingB B p) p
    (TensorProduct.liftAddHom (adicPolynomialPairing A B δ ι p conn degree) sorry)

variable (M) in
/-- The completed target terms include `M ⊗̂[D] D'` in degree zero. -/
noncomputable def adicPolynomialTerm (degree : ℕ) : AddCommGrpCat :=
  AddCommGrpCat.of
    (completedTensorB (completedRingB B p) p M (completedPolynomialForm A B δ ι p degree))

/-- The completed de Rham complex after scalar extension, with its induced connection. -/
noncomputable def adicPolynomialComplex (conn : Connection.Adic A B δ p M)
    (hconn : Connection.Adic.IsIntegrable A B δ p conn) : CochainComplex AddCommGrpCat ℕ :=
  CochainComplex.of (adicPolynomialTerm A B δ ι p M)
    (fun degree ↦ AddCommGrpCat.ofHom (adicPolynomialDifferential A B δ ι p conn degree))
    (fun _ ↦ sorry)

variable (M) in
/-- The completed comparison components extend coefficients in degree zero and forms thereafter. -/
noncomputable def adicComparisonComponent :
    (degree : ℕ) → Connection.Adic.term A B δ p M degree ⟶
      adicPolynomialTerm A B δ ι p M degree
  | 0 => AddCommGrpCat.ofHom
      ((AdicCompletion.of (principalIdealB (completedRingB B p) p) _).comp
        ((TensorProduct.mk (completedRingB B p) M
          (completedPolynomialForm A B δ ι p 0)).flip
          (AdicCompletion.of (principalIdealB B p) (DPPolynomial B ι) 1))).toAddMonoidHom
  | degree + 1 => AddCommGrpCat.ofHom
      (AdicCompletion.map (principalIdealB (completedRingB B p) p)
        (TensorProduct.map (LinearMap.id : M →ₗ[completedRingB B p] M)
          (completedFormComparison A B δ ι p (degree + 1)))).toAddMonoidHom

/-- The comparison from an arbitrary completed-valued integrable connection. -/
noncomputable def adicComparison (conn : Connection.Adic A B δ p M)
    (hconn : Connection.Adic.IsIntegrable A B δ p conn) :
    Connection.Adic.deRhamComplex A B δ p conn hconn ⟶
      adicPolynomialComplex A B δ ι p conn hconn :=
  CochainComplex.ofHom (adicComparisonComponent A B δ ι p M) (fun _ ↦ sorry)

/-- The degree-zero target is completed coefficient extension to the p-adic polynomial ring. -/
theorem adicPolynomialTerm_zero :
    adicPolynomialTerm A B δ ι p M 0 =
      AddCommGrpCat.of
        (completedTensorB (completedRingB B p) p M
          (AdicCompletion (principalIdealB B p) (DPPolynomial B ι))) := sorry

/-- The completed polynomial complex has the explicitly constructed target terms. -/
theorem adicPolynomialComplex_X (conn : Connection.Adic A B δ p M)
    (hconn : Connection.Adic.IsIntegrable A B δ p conn) (degree : ℕ) :
    (adicPolynomialComplex A B δ ι p conn hconn).X degree =
      adicPolynomialTerm A B δ ι p M degree := sorry

/-- The completed comparison has the specified coefficient-and-form components. -/
theorem adicComparison_component (conn : Connection.Adic A B δ p M)
    (hconn : Connection.Adic.IsIntegrable A B δ p conn) (degree : ℕ) :
    (adicComparison A B δ ι p conn hconn).f degree =
      adicComparisonComponent A B δ ι p M degree := sorry

/-- The induced differential obeys the tensor Leibniz formula, including in degree zero. -/
theorem adicPolynomialDifferential_tmul (conn : Connection.Adic A B δ p M) (degree : ℕ)
    (element : M) (form : completedPolynomialForm A B δ ι p degree) :
    adicPolynomialDifferential A B δ ι p conn degree
        (AdicCompletion.of (principalIdealB (completedRingB B p) p) _
          (element ⊗ₜ[completedRingB B p] form)) =
      adicPolynomialPairing A B δ ι p conn degree element form := sorry

/-- Degree-zero completed comparison is the completed coefficient-extension map. -/
theorem adicComparison_zero (conn : Connection.Adic A B δ p M)
    (hconn : Connection.Adic.IsIntegrable A B δ p conn) (element : M) :
    (adicComparison A B δ ι p conn hconn).f 0 element =
      AdicCompletion.of (principalIdealB (completedRingB B p) p) _
        (element ⊗ₜ[completedRingB B p]
          AdicCompletion.of (principalIdealB B p) (DPPolynomial B ι) 1) := sorry

/-- p-adic completion preserves the de Rham comparison for completed-valued connections. -/
theorem dpPolynomial_completedDeRhamComparison_quasiIso
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {J : Ideal B} (δ : DividedPowers J) (ι : Type u) (p : ℕ)
    {M : Type u} [AddCommGroup M] [Module (completedRingB B p) M]
    [IsAdicComplete (principalIdealB (completedRingB B p) p) M]
    (conn : Connection.Adic A B δ p M)
    (hconn : Connection.Adic.IsIntegrable A B δ p conn) :
    QuasiIso (adicComparison A B δ ι p conn hconn) := sorry

end CompletedComparison

end DPPolynomial.DeRham

end
