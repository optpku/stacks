/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.FiniteType.FibreComponents
import StacksCheckRecall

@[expose] public section

universe u

open PrimeSpectrum

/- Exercise 111.21.1 -/
@[stacks 0CVR] #check
  (ProductFibre.closedFibre_ncard : ∀ (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ),
    (n = 0 →
      Function.Injective (ProductFibre.algebraMapUnit k) ∧
        (ProductFibre.algebraMapUnit k).FiniteType ∧
        IsDomain (ProductFibre.UnitRing k) ∧
        (irreducibleComponents
          (PrimeSpectrum (ProductFibre.closedFibreUnit k))).encard = (0 : ℕ∞)) ∧
    (0 < n →
      Function.Injective (ProductFibre.algebraMapProduct k n) ∧
        (ProductFibre.algebraMapProduct k n).FiniteType ∧
        IsDomain (ProductFibre.ProductRing k n) ∧
        (irreducibleComponents
          (PrimeSpectrum (ProductFibre.closedFibreProduct k n))).encard =
          (n : ℕ∞)))

#check
  (AllClosedFibres.closedFibre_reducible : ∀ (k : Type u) [Field k] [IsAlgClosed k],
    Function.Injective (AllClosedFibres.algebraMap k) ∧
      (AllClosedFibres.algebraMap k).FiniteType ∧
      IsDomain (AllClosedFibres.Ring k) ∧
      ∀ α : k, Nonempty (PrimeSpectrum (AllClosedFibres.closedFibre k α)) ∧
        ¬ IrreducibleSpace (PrimeSpectrum (AllClosedFibres.closedFibre k α)))

#check
  (OriginFibre.closedFibre_irreducible_of_ne_zero :
    ∀ (k : Type u) [Field k] [IsAlgClosed k],
      Function.Injective (OriginFibre.algebraMap k) ∧
        (OriginFibre.algebraMap k).FiniteType ∧
        IsDomain (OriginFibre.Ring k) ∧
        (∀ α β : k, (α, β) ≠ (0, 0) →
          IrreducibleSpace (PrimeSpectrum (OriginFibre.closedFibre k α β))) ∧
        Nonempty (PrimeSpectrum (OriginFibre.closedFibre k 0 0)) ∧
        ¬ IrreducibleSpace (PrimeSpectrum (OriginFibre.closedFibre k 0 0)))
