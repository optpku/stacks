/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.NormalForm
import StacksCheckRecall

@[expose] public section

universe u v w x

namespace RingHom.Etale

/- Lemma 58.32.1: in positive characteristic, a positive normal-form invariant for an étale
polynomial presentation can be strictly decreased while preserving the finite étale quotient
diagram. -/
@[stacks 0G1F] #check (RingHom.Etale.exists_normalForm_lt :
    ∀
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
    (h_normalForm : 0 < normalForm q phi tau),
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
        normalForm q phi' tau' < normalForm q phi tau)

end RingHom.Etale
