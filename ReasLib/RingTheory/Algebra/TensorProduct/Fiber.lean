/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fibers and compatible primes of tensor products

This file owns the canonical fiber comparison for a tensor-product base change and the existence
of a tensor-product prime above two compatible primes.

@stack 05LL
-/

@[expose] public section

open scoped TensorProduct

universe u v x

namespace Algebra.TensorProduct

variable {R : Type u} {S : Type v} {R' : Type x}
variable [CommRing R] [CommRing S] [CommRing R'] [Algebra R S] [Algebra R R']

/-- The fiber of `R' ⊗[R] S` over a prime of `R'` is the scalar extension of `S` to the
corresponding residue field. -/
@[stacks 05LL "fiber of a tensor-product base change"]
noncomputable abbrev fiberRightAlgEquiv (p' : PrimeSpectrum R') :
    p'.asIdeal.Fiber (R' ⊗[R] S) ≃ₐ[p'.asIdeal.ResidueField]
      p'.asIdeal.ResidueField ⊗[R] S :=
  cancelBaseChange R R' p'.asIdeal.ResidueField p'.asIdeal.ResidueField S

-- Local instance justification (instance diamond): the left-ordered tensor product uses `R'` as
-- its right scalar ring in the contraction formulas.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Compatible primes of two `R`-algebras lift to a prime of their tensor product. -/
@[stacks 05LL "compatible prime of a tensor product"]
theorem existsPrimeOver (q : PrimeSpectrum S) (p' : PrimeSpectrum R')
    (hcompat : PrimeSpectrum.comap (algebraMap R R') p' =
      PrimeSpectrum.comap (algebraMap R S) q) :
    ∃ q' : PrimeSpectrum (S ⊗[R] R'),
      PrimeSpectrum.comap (algebraMap S (S ⊗[R] R')) q' = q ∧
        PrimeSpectrum.comap (algebraMap R' (S ⊗[R] R')) q' = p' := sorry

end Algebra.TensorProduct
