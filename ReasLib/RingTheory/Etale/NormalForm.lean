/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.RingHom.Etale
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

noncomputable section

universe u v w x

namespace RingHom.Etale

/-- The normal-form invariant of an étale polynomial presentation is the least difference
`r - s` among finite generating families whose first `s` members form a maximal integral
prefix over the image of the polynomial algebra map. -/
noncomputable def normalForm
    {k : Type u} {A : Type v} {B : Type w} {C : Type x}
    [CommRing k] [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C] {n : ℕ}
    (q : MvPolynomial (Fin n) k →ₐ[k] A)
    (phi : MvPolynomial (Fin n) k →ₐ[k] C)
    (tau : C ⧸ Ideal.map phi.toRingHom (RingHom.ker q.toRingHom) →ₐ[k] B) : ℕ :=
  let _ := tau
  sInf {d : ℕ |
    ∃ (r s : ℕ) (y : Fin r → C) (hs : s ≤ r),
      Algebra.adjoin k (Set.range phi ∪ Set.range y) = ⊤ ∧
      (∀ i : Fin s,
        phi.toRingHom.IsIntegralElem (y (Fin.castLE hs i))) ∧
      (∀ (t : ℕ) (ht : t ≤ r), s < t →
        ¬ ∀ i : Fin t,
          phi.toRingHom.IsIntegralElem (y (Fin.castLE ht i))) ∧
      d = r - s}

/-- The defining minimum characterization of `normalForm`. -/
theorem normalForm_spec
    {k : Type u} {A : Type v} {B : Type w} {C : Type x}
    [CommRing k] [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C] {n : ℕ}
    (q : MvPolynomial (Fin n) k →ₐ[k] A)
    (phi : MvPolynomial (Fin n) k →ₐ[k] C)
    (tau : C ⧸ Ideal.map phi.toRingHom (RingHom.ker q.toRingHom) →ₐ[k] B) :
    normalForm q phi tau =
      sInf {d : ℕ |
        ∃ (r s : ℕ) (y : Fin r → C) (hs : s ≤ r),
          Algebra.adjoin k (Set.range phi ∪ Set.range y) = ⊤ ∧
          (∀ i : Fin s,
            phi.toRingHom.IsIntegralElem (y (Fin.castLE hs i))) ∧
          (∀ (t : ℕ) (ht : t ≤ r), s < t →
            ¬ ∀ i : Fin t,
              phi.toRingHom.IsIntegralElem (y (Fin.castLE ht i))) ∧
          d = r - s} := sorry

/-- An étale polynomial presentation has normal form zero exactly when its structure map is
finite. -/
theorem normalForm_zero_iff_finite
    {k : Type u} {A : Type v} {B : Type w} {C : Type x}
    [CommRing k] [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C] {n : ℕ}
    (q : MvPolynomial (Fin n) k →ₐ[k] A)
    (phi : MvPolynomial (Fin n) k →ₐ[k] C)
    (tau : C ⧸ Ideal.map phi.toRingHom (RingHom.ker q.toRingHom) →ₐ[k] B)
    (h_phi : RingHom.Etale phi.toRingHom) :
    normalForm q phi tau = 0 ↔ RingHom.Finite phi.toRingHom := sorry

/-- In positive characteristic, a positive normal-form invariant for an étale polynomial
presentation can be strictly decreased while preserving its finite étale quotient diagram. -/
@[stacks 0G1F]
theorem exists_normalForm_lt
    {k : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Field k] [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C]
    (p n : ℕ) [CharP k p] (h_positiveChar : 0 < p)
    (q : MvPolynomial (Fin n) k →ₐ[k] A)
    (pi : A →ₐ[k] B)
    (phi : MvPolynomial (Fin n) k →ₐ[k] C)
    (tau : C ⧸ Ideal.map phi.toRingHom (RingHom.ker q.toRingHom) →ₐ[k] B)
    (alpha : A →ₐ[k] C ⧸ Ideal.map phi.toRingHom (RingHom.ker q.toRingHom))
    (h_q : Function.Surjective q)
    (h_pi_finite : RingHom.Finite pi.toRingHom)
    (h_pi_etale : RingHom.Etale pi.toRingHom)
    (h_phi_etale : RingHom.Etale phi.toRingHom)
    (h_tau : Function.Surjective tau)
    (h_alpha_q : alpha.comp q =
      (Ideal.Quotient.mkₐ k
        (Ideal.map phi.toRingHom (RingHom.ker q.toRingHom))).comp phi)
    (h_tau_alpha : tau.comp alpha = pi)
    (h_normalForm : 0 < normalForm q phi tau) :
    ∃ (phi' : MvPolynomial (Fin n) k →ₐ[k] C)
      (tau' : C ⧸ Ideal.map phi'.toRingHom (RingHom.ker q.toRingHom) →ₐ[k] B)
      (alpha' : A →ₐ[k]
        C ⧸ Ideal.map phi'.toRingHom (RingHom.ker q.toRingHom)),
      RingHom.Etale phi'.toRingHom ∧
        Function.Surjective tau' ∧
        alpha'.comp q =
          (Ideal.Quotient.mkₐ k
            (Ideal.map phi'.toRingHom (RingHom.ker q.toRingHom))).comp phi' ∧
        tau'.comp alpha' = pi ∧
        normalForm q phi' tau' < normalForm q phi tau := sorry

end RingHom.Etale
