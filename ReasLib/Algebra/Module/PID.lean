module

public import Mathlib.Algebra.Module.PID
public import ReasLib.RingTheory.Ideal.Principal
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite modules over principal ideal domains

@stack 0ASV

This leaf exposes the source-shaped cyclic decomposition as a bridge to
`Module.equiv_free_prod_directSum`.  Mathlib's prime-power decomposition remains
the canonical stronger owner; the bridge only forgets the extra factorization
data and rewrites cyclic ideals through `principalIdeal`.
-/

open scoped DirectSum

universe u v

namespace Module

/-- Lemma 15.125.9: a finite module over a principal ideal domain is a product of a finite free
module and finitely many cyclic quotients by nonzero principal ideals. -/
@[stacks 0ASV "Lemma 15.125.9, finite module decomposition over a PID"]
theorem exists_equiv_free_prod_directSum_principalQuotients
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (r : ℕ) (ι : Type u) (_ : Fintype ι) (f : ι → R),
      (∀ i, f i ≠ 0) ∧
        Nonempty (M ≃ₗ[R] (Fin r →₀ R) × ⨁ i : ι, R ⧸ principalIdeal (f i)) := sorry
-- Proof strategy: start from Mathlib's
-- `Module.equiv_free_prod_directSum`, retain its finite torsion index and
-- nonzero prime-power generators, and rewrite each cyclic ideal as
-- `principalIdeal (f i)`.  Package the existing linear equivalence without
-- choosing any additional invariant-factor representatives.

end Module
