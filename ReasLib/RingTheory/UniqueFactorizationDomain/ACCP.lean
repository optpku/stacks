/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.UniqueFactorizationDomain.Factorization

/-!
# Factorization from ACCP

The ascending-chain condition on principal ideals is exposed as a direct bridge to the
canonical `WfDvdMonoid` factorization API.  The bridge is stated over commutative semirings;
the source-facing domain instance is a specialization of this reusable result.
-/

@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [CommSemiring R] [IsDomain R]

/-- Lemma 10.120.3 (Stacks `034R`): under the ascending-chain condition on principal ideals, every
nonzero nonunit element has a finite factorization into irreducible elements. -/
@[stacks 034R]
theorem exists_irreducible_factorization_of_accp
    (hacc : {I : Ideal R | I.IsPrincipal}.WellFoundedOn (· > ·))
    {a : R} (ha0 : a ≠ 0) (ha : ¬ IsUnit a) :
    ∃ f : Multiset R, (∀ b ∈ f, Irreducible b) ∧ f.prod = a := sorry

/-- The ACCP hypothesis packages all of the preceding elementwise factorizations into the
predicate-level interface used by unique-factorization criteria. -/
@[stacks 034R "predicate bridge"]
theorem hasIrreducibleFactorizations_of_accp
    (hacc : {I : Ideal R | I.IsPrincipal}.WellFoundedOn (· > ·)) :
    UniqueFactorizationMonoid.HasIrreducibleFactorizations R := sorry

end Ideal
