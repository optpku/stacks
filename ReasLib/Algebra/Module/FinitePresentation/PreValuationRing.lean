module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReasLib.RingTheory.Ideal.Principal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite presentation over generalized valuation rings

This leaf owns the cyclic decomposition of finitely presented modules over a
`PreValuationRing`.  The isomorphism remains under the genuine existential
quantifier from the source; no canonical decomposition is chosen.

@stack 0ASP
-/

@[expose] public section

open scoped DirectSum

universe u v

namespace Module.FinitePresentation

/-- Lemma 15.125.3 (0ASP): every finitely presented module over a generalized
valuation ring is a finite direct sum of principal quotient modules. -/
@[stacks 0ASP "finite cyclic decomposition over a generalized valuation ring"]
theorem exists_linearEquiv_directSum_principalQuotients_of_preValuationRing
    {R : Type u} [CommRing R] [PreValuationRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] :
    ∃ (n : ℕ) (f : Fin n → R),
      Nonempty (M ≃ₗ[R] ⨁ i : Fin n, R ⧸ principalIdeal (f i)) := sorry
-- Proof strategy: induct on the finite dimension of
-- `M ⧸ IsLocalRing.maximalIdeal R • ⊤`.  Choose a residue-basis lift with
-- minimal cyclic annihilator, identify its cyclic span with a principal
-- quotient, and prove that its inclusion is principal-pure using total
-- divisibility.  The lifting criterion from tag 0ASM splits that span; apply
-- the induction hypothesis to the quotient and combine the finite direct sums.

end Module.FinitePresentation
