/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import ReasLib.RingTheory.KrullDimension.Fiber.MinimalPrime

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- A finite-type algebra admits an étale neighborhood preserving a selected
prime's residue field, with finite singleton-fiber factors and a remainder
whose minimal-prime fiber components are positive-dimensional. -/
theorem exists_etale_finiteProductDecomposition
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (p : PrimeSpectrum R) :
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
            Algebra.Fiber.minimalPrimesPositiveDimensional (S := C) p' := sorry

end Algebra
