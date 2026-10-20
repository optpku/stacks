/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Morphisms.Etale.Complement
public import ReasLib.RingTheory.AdicCompletion.RigEtale.EtaleOverComplement

/-!
# Completions of finite-type algebras étale away from V(I)

Lemma 88.8.4 relates étaleness of a finite-type algebra over `Spec(A) \ V(I)`
with rig-étaleness of its `I`-adic completion in the sense of Lemma 88.8.2.
-/

@[expose] public section

universe u

open Algebra Algebra.NaiveCotangent.Adic AlgebraicGeometry

/- Lemma 88.8.4 -/
@[stacks 0ALQ] #check (Algebra.RigEtale.of_isEtaleOverComplement :
  {A : Type u} → [CommRing A] → [IsNoetherianRing A] → (I : Ideal A) →
    (B : Type u) → [CommRing B] → [Algebra A B] → [FiniteType A B] →
      Algebra.IsEtaleOverComplement I B →
        Algebra.RigEtale I (Algebra.NaiveCotangent.Adic.algebraCompletion I B))

@[stacks 0ALQ] #check (Algebra.RigEtale.exists_mem_oneAdd_isEtaleOverComplement :
  {A : Type u} → [CommRing A] → [IsNoetherianRing A] → (I : Ideal A) →
    (B : Type u) → [CommRing B] → [Algebra A B] → [FiniteType A B] →
      [Algebra.RigEtale I (Algebra.NaiveCotangent.Adic.algebraCompletion I B)] →
        ∃ g ∈ (I.map (algebraMap A B)).oneAdd,
          Algebra.IsEtaleOverComplement I (Localization.Away g))

#check (Algebra.isEtaleOverComplement_iff_morphismRestrict :
  {A : Type u} → [CommRing A] → [IsNoetherianRing A] → (I : Ideal A) →
    (B : Type u) → [CommRing B] → [Algebra A B] → [FiniteType A B] →
      Algebra.IsEtaleOverComplement I B ↔
        AlgebraicGeometry.Etale
          (Spec.map (CommRingCat.ofHom (algebraMap A B)) ∣_
            ⟨(PrimeSpectrum.zeroLocus (I : Set A))ᶜ,
              (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩))
