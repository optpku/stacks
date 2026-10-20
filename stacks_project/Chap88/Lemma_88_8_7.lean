/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.AdicCompletion.RigEtale.EtaleOverComplement

/-!
# Algebraization of maps of adic completions through pair henselization

Lemma 88.8.7 records unique descent of completion maps and factorization through
an étale algebra inducing an isomorphism on the closed fiber.
-/

@[expose] public section

universe u

open Algebra RingPairCat

/- Lemma 88.8.7 (1). -/
@[stacks 0AKJ] #check (Algebra.IsEtaleOverComplement.existsUnique_algHom :
  ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [IsNoetherianRing A] [IsNoetherianRing C]
    [FiniteType A B] [henselianPairInclusion.IsRightAdjoint]
    (I : Ideal A) (hB : IsEtaleOverComplement I B)
    (φ : AdicCompletion (I.map (algebraMap A B)) B →ₐ[A]
      AdicCompletion (I.map (algebraMap A C)) C),
    ∃! ψ : B →ₐ[A] henselizationRing (pairOfIdeal (I.map (algebraMap A C))),
      φ.toRingHom.comp (algebraMap B (AdicCompletion (I.map (algebraMap A B)) B)) =
        (henselizationToAdicCompletion
            (pairOfIdeal (I.map (algebraMap A C)))).comp ψ.toRingHom)

/- Lemma 88.8.7 (2). -/
@[stacks 0AKJ] #check (Algebra.IsEtaleOverComplement.exists_etaleFactor :
  ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [IsNoetherianRing A] [IsNoetherianRing C]
    [FiniteType A B] [henselianPairInclusion.IsRightAdjoint]
    (I : Ideal A) (hB : IsEtaleOverComplement I B)
    (ψ : B →ₐ[A] henselizationRing (pairOfIdeal (I.map (algebraMap A C)))),
    ∃ (C' : Type u) (_ : CommRing C') (_ : Algebra A C') (_ : Algebra C C')
      (_ : IsScalarTower A C C') (_ : Algebra.Etale C C'),
      Function.Bijective
          (AlgHom.BaseIdeal.quotientMap (IsScalarTower.toAlgHom A C C') I) ∧
        ∃ (τ : C' →ₐ[C] henselizationRing (pairOfIdeal (I.map (algebraMap A C))))
          (φ : B →ₐ[A] C'),
          ψ = (τ.restrictScalars A).comp φ)
