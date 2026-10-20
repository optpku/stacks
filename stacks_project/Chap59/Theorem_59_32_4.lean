/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Henselian.Decomposition
import StacksCheckRecall

@[expose] public section

universe u

open IsLocalRing Polynomial


/- Theorem 59.32.4: the five equivalent henselian local-ring criteria are
recorded by the shared decomposition characterization. -/
@[stacks 03QH] #check (HenselianLocalRing.decompositionTfae :
  ∀ (R : Type u) [CommRing R] [IsLocalRing R],
    List.TFAE
      [ HenselianLocalRing R
      , ∀ f : R[X],
          ∀ g h : (ResidueField R)[X],
            f.map (residue R) = g * h →
            IsCoprime g h →
            ∃ g' h' : R[X],
              f = g' * h' ∧
              g'.map (residue R) = g ∧
              h'.map (residue R) = h
      , ∀ (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S],
          ∃ (ι : Type u) (_ : Fintype ι) (B : ι → Type u)
            (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra R (B i))
            (_ : ∀ i, IsLocalRing (B i)) (_ : ∀ i, Module.Finite R (B i)),
            Nonempty (S ≃ₐ[R] (∀ i, B i))
      , ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.FiniteType R S],
          ∃ (ι : Type u) (_ : Fintype ι) (B : ι → Type u)
            (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra R (B i))
            (_ : ∀ i, IsLocalRing (B i)) (_ : ∀ i, Module.Finite R (B i))
            (C : Type u) (_ : CommRing C) (_ : Algebra R C),
            Nonempty (S ≃ₐ[R] ((∀ i, B i) × C)) ∧
              Algebra.Fiber.minimalPrimesPositiveDimensional
                (S := C) (IsLocalRing.closedPoint R)
      , ∀ (A : Type u) [CommRing A] [Algebra R A] [Algebra.Etale R A]
          (n : Ideal A) [n.IsMaximal] [n.LiesOver (maximalIdeal R)],
          Nonempty (ResidueField R ≃ₐ[R] (A ⧸ n)) →
            ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra R A')
              (φ : A ≃ₐ[R] R × A'),
              Ideal.map φ.toRingEquiv.toRingHom n =
                Ideal.prod (maximalIdeal R) (⊤ : Ideal A') ])
