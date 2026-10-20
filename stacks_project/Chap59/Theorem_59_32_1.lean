/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.Neighborhood.FiniteDecomposition
import StacksCheckRecall

@[expose] public section

universe u v

open scoped TensorProduct

/- Theorem 59.32.1: a finite-type algebra admits the stated finite-product
decomposition after an etale neighborhood of a selected prime. -/
@[stacks 03QE]
#check
  (Algebra.exists_etale_finiteProductDecomposition :
    ∀ {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
      [Algebra.FiniteType R S] (p : PrimeSpectrum R),
      ∃ (A : CommAlgCat.{u} R) (p' : PrimeSpectrum A)
        (h_over : p.asIdeal = Ideal.comap (algebraMap R A) p'.asIdeal),
        Algebra.Etale R A ∧
          Function.Bijective
            (Ideal.ResidueField.map p.asIdeal p'.asIdeal (algebraMap R A) h_over) ∧
          ∃ (n : ℕ) (B : Fin n → CommAlgCat.{max u v} A)
            (C : CommAlgCat.{max u v} A),
            Nonempty ((A ⊗[R] S) ≃ₐ[A] ((i : Fin n) → B i) × C) ∧
              (∀ i, Module.Finite A (B i) ∧
                ∃! q : PrimeSpectrum (B i),
                  p'.asIdeal = Ideal.comap (algebraMap A (B i)) q.asIdeal) ∧
              Algebra.Fiber.minimalPrimesPositiveDimensional (S := C) p')
