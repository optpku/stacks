/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.UniqueFactorizationDomain.ACCP
import StacksCheckRecall

/-!
# Irreducible Factorization from ACCP

@stack 034R
-/

@[expose] public section

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/- Lemma 10.120.3 (Stacks `034R`): the ACCP factorization statement is owned by the reusable
`Ideal.exists_irreducible_factorization_of_accp` bridge. -/
@[stacks 034R]
#check (Ideal.exists_irreducible_factorization_of_accp (R := R) :
  {I : Ideal R | I.IsPrincipal}.WellFoundedOn (· > ·) →
    ∀ {a : R}, a ≠ 0 → ¬ IsUnit a →
      ∃ f : Multiset R, (∀ b ∈ f, Irreducible b) ∧ f.prod = a)

@[stacks 034R "ACCP irreducible-factorization class"]
#check (Ideal.hasIrreducibleFactorizations_of_accp (R := R) :
  {I : Ideal R | I.IsPrincipal}.WellFoundedOn (· > ·) →
    UniqueFactorizationMonoid.HasIrreducibleFactorizations R)
