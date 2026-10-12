/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap60.Remark_60_6_7_Forms
public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers.Polynomial
public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import StacksCheckRecall
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open scoped TensorProduct

universe u v

/- Lemma 60.6.2 (1) -/
@[stacks 07HS] #check (KaehlerDifferential.DeRham.dividedPowerDifferential_polynomial :
    ∀ {A : Type u} [CommRing A] {B : Type v} [CommRing B]
    (f : A →+* B) {J : Ideal B} (δ : DividedPowers J)
    (δx : DividedPowers (J.map (algebraMap B (Polynomial B))))
    (hδx : DividedPowers.IsDPMorphism δ δx (algebraMap B (Polynomial B))),
    Nonempty (dividedPowerDifferential ((algebraMap B (Polynomial B)).comp f) δx ≃ₗ[Polynomial B]
      ((Polynomial B ⊗[B] dividedPowerDifferential f δ) × Polynomial B)))

/- Lemma 60.6.2 (2) -/
@[stacks 07HS] #check (KaehlerDifferential.DeRham.dividedPowerDifferential_dpPolynomial :
    ∀ {A : Type u} [CommRing A] {B : Type v} [CommRing B]
    (f : A →+* B) {J : Ideal B} (δ : DividedPowers J),
    Nonempty (dividedPowerDifferential
      ((algebraMap B (DPPolynomial.Finite.Ring B 1)).comp f)
      (DPPolynomial.Finite.dividedPowers δ) ≃ₗ[DPPolynomial.Finite.Ring B 1]
      ((DPPolynomial.Finite.Ring B 1 ⊗[B] dividedPowerDifferential f δ) ×
        DPPolynomial.Finite.Ring B 1)))

/- Lemma 60.6.2 (3) -/
@[stacks 07HS] #check (KaehlerDifferential.DeRham.dividedPowerDifferential_quotient :
    ∀ {A : Type u} [CommRing A] {B : Type v} [CommRing B]
    (f : A →+* B) {J : Ideal B} (δ : DividedPowers J)
    (K : Ideal B) (hKsub : K ≤ J)
    (hK : DividedPowers.IsSubDPIdeal δ (K ⊓ J)),
    Nonempty (
      dividedPowerDifferential ((Ideal.Quotient.mk K).comp f)
          (DividedPowers.Quotient.dividedPowers δ hK) ≃ₗ[B ⧸ K]
      (((B ⧸ K) ⊗[B] dividedPowerDifferential f δ) ⧸
        Submodule.span (B ⧸ K)
          {ω | ∃ k : B, k ∈ K ∧
            ω = (1 : B ⧸ K) ⊗ₜ[B] dividedPowerDifferentialDerivation f δ k})))
