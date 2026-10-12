/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Localization.Away.Equiv

@[expose] public section

/-!
# Finite polynomial factorizations away from one element

This leaf owns the factorization produced by relative Noether normalization:
an injective finite polynomial map into an intermediate subalgebra whose map to
the ambient algebra becomes an isomorphism after inverting one base element.
-/

namespace MvPolynomial.NoetherNormalization

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A finite injective polynomial factorization through an intermediate `R`-subalgebra that
becomes an isomorphism onto `S` after inverting `f`. -/
@[stacks 07NA "injective polynomial factorization away from one element"]
structure IsFactorizationAway
    (d : ℕ) (S' : Subalgebra R S)
    (polynomial : MvPolynomial (Fin d) R →ₐ[R] S') (f : R) : Prop where
  polynomial_injective : Function.Injective polynomial
  polynomial_finite : AlgHom.Finite polynomial
  away_ne_zero : f ≠ 0
  away_bijective :
    Function.Bijective (Localization.awayMapₐ S'.val (algebraMap R S' f))

namespace IsFactorizationAway

/-- The canonical algebra equivalence between the two principal localizations in a factorization
away from `f`. -/
@[stacks 07NA "principal-localization equivalence of a factorization"]
noncomputable def awayEquiv
    {d : ℕ} {S' : Subalgebra R S} {polynomial : MvPolynomial (Fin d) R →ₐ[R] S'} {f : R}
    (h : IsFactorizationAway d S' polynomial f) :
    Localization.Away (algebraMap R S' f) ≃ₐ[R]
      Localization.Away (S'.val (algebraMap R S' f)) :=
  Localization.Away.algEquivOfBijective S'.val (algebraMap R S' f) h.away_bijective

/-- The four defining conditions of `IsFactorizationAway` as a directly consumable conjunction. -/
theorem spec
    {d : ℕ} {S' : Subalgebra R S} {polynomial : MvPolynomial (Fin d) R →ₐ[R] S'} {f : R}
    (h : IsFactorizationAway d S' polynomial f) :
    Function.Injective polynomial ∧ AlgHom.Finite polynomial ∧ f ≠ 0 ∧
      Function.Bijective (Localization.awayMapₐ S'.val (algebraMap R S' f)) := sorry

end IsFactorizationAway

/-- Lemma 10.115.7, tag 07NA: an injective finite-type map from a domain admits a finite
injective polynomial factorization away from a nonzero base element. -/
@[stacks 07NA]
theorem exists_factorizationAway
    [IsDomain R] [Algebra.FiniteType R S]
    (hinj : Function.Injective (algebraMap R S)) :
    ∃ (d : ℕ) (S' : Subalgebra R S)
      (polynomial : MvPolynomial (Fin d) R →ₐ[R] S') (f : R),
      IsFactorizationAway d S' polynomial f := sorry

end MvPolynomial.NoetherNormalization
