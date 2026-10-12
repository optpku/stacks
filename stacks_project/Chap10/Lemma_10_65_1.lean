/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import ReasLib.RingTheory.RingHom.Fiber.Quotient
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Localization
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Quotient
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Filtration
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Relative
public import ReasLib.Algebra.Module.Torsion.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Relative assassins and finite witnesses

@stack 05GB

This file records the six sets compared in Lemma 10.65.1 and exposes the
source comparison as atomic statements. The reusable relative-assassin owner
is `relativeAssassin` from
`ReasLib.RingTheory.Ideal.AssociatedPrime.Relative`.
-/

@[expose] public section

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w x

section Definitions

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {N : Type w} [AddCommGroup N] [Module S N]

/-- The quotient module `N / pN` used in the finite descriptions of the relative assassin. -/
abbrev relativeAssassinPrimeQuotient
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (N : Type w) [AddCommGroup N] [Module S N] (p : Ideal R) : Type w :=
  N ⧸ (Ideal.map (algebraMap R S) p) • (⊤ : Submodule S N)

/-- The fiber-spectrum image `A'` associated to `N` over `R → S`. -/
abbrev relativeAssassinAprime
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (N : Type w) [AddCommGroup N] [Module S N] : Set (PrimeSpectrum S) :=
  ⋃ p : PrimeSpectrum R,
    PrimeSpectrum.comap (algebraMap S (p.asIdeal.Fiber S)) ''
      {q : PrimeSpectrum (p.asIdeal.Fiber S) |
        q.asIdeal ∈ associatedPrimesOfModule (p.asIdeal.Fiber S)
          ((p.asIdeal.Fiber S) ⊗[S] N)}

/-- Membership in `A'` in terms of a point of a fiber spectrum. -/
@[simp]
theorem mem_relativeAssassinAprime_iff (q : PrimeSpectrum S) :
    q ∈ relativeAssassinAprime R S N ↔
      ∃ p : PrimeSpectrum R,
        q ∈ PrimeSpectrum.comap (algebraMap S (p.asIdeal.Fiber S)) ''
          {q' : PrimeSpectrum (p.asIdeal.Fiber S) |
            q'.asIdeal ∈ associatedPrimesOfModule (p.asIdeal.Fiber S)
              ((p.asIdeal.Fiber S) ⊗[S] N)} := sorry

/-- The finite quotient description `A_fin` of the relative assassin. -/
abbrev relativeAssassinAfin
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (N : Type w) [AddCommGroup N] [Module S N] : Set (PrimeSpectrum S) :=
  {q : PrimeSpectrum S |
    q.asIdeal ∈ associatedPrimesOfModule S
      (relativeAssassinPrimeQuotient R S N (q.asIdeal.under R))}

/-- Membership in `A_fin` is association to the quotient by the contracted prime. -/
@[simp]
theorem mem_relativeAssassinAfin_iff (q : PrimeSpectrum S) :
    q ∈ relativeAssassinAfin R S N ↔
      q.asIdeal ∈ associatedPrimesOfModule S
        (relativeAssassinPrimeQuotient R S N (q.asIdeal.under R)) := sorry

/-- The finite union `A'_fin` over prime quotients of `R`. -/
abbrev relativeAssassinAprimeFin
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (N : Type w) [AddCommGroup N] [Module S N] : Set (PrimeSpectrum S) :=
  {q : PrimeSpectrum S |
    ∃ p : PrimeSpectrum R,
      q.asIdeal ∈ associatedPrimesOfModule S
        (relativeAssassinPrimeQuotient R S N p.asIdeal)}

/-- Membership in `A'_fin` is association to `N / pN` for some prime `p` of `R`. -/
@[simp]
theorem mem_relativeAssassinAprimeFin_iff (q : PrimeSpectrum S) :
    q ∈ relativeAssassinAprimeFin R S N ↔
      ∃ p : PrimeSpectrum R,
        q.asIdeal ∈ associatedPrimesOfModule S
          (relativeAssassinPrimeQuotient R S N p.asIdeal) := sorry

end Definitions

section Comparisons

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {N : Type w} [AddCommGroup N] [Module S N] [Module R N]
variable [IsScalarTower R S N]

/-- The set `B` obtained by tensoring `N` with an arbitrary `R`-module. -/
abbrev relativeAssassinB
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    Set (PrimeSpectrum S) :=
  {q : PrimeSpectrum S |
    ∃ (M : Type (max u v w x)) (_ : AddCommGroup M) (_ : Module R M),
      q.asIdeal ∈ associatedPrimesOfModule S (N ⊗[R] M)}

/-- The set `B_fin` obtained by tensoring `N` with a finite `R`-module. -/
abbrev relativeAssassinBfin
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    Set (PrimeSpectrum S) :=
  {q : PrimeSpectrum S |
    ∃ (M : Type (max u v w x)) (_ : AddCommGroup M) (_ : Module R M)
      (_ : Module.Finite R M),
      q.asIdeal ∈ associatedPrimesOfModule S (N ⊗[R] M)}

/-- Lemma 10.65.1 (1): the relative assassin `A` agrees with the fiber image `A'`. -/
@[stacks 05GB "(1)"]
theorem relativeAssassinA_eq_relativeAssassinAprime :
    relativeAssassin R S N = relativeAssassinAprime R S N := sorry

/-- Lemma 10.65.1 (2): `A_fin` is contained in `A`. -/
@[stacks 05GB "(2)"]
theorem relativeAssassinAfin_subset_relativeAssassinA :
    relativeAssassinAfin R S N ⊆ relativeAssassin R S N := sorry

/-- Lemma 10.65.1 (3): `B_fin` is contained in `B`. -/
@[stacks 05GB "(3)"]
theorem relativeAssassinBfin_subset_relativeAssassinB :
    relativeAssassinBfin.{u, v, w, x} R S N ⊆
      relativeAssassinB.{u, v, w, x} R S N := sorry

/-- Lemma 10.65.1 (4): `A_fin` is contained in `A'_fin`. -/
@[stacks 05GB "(4)"]
theorem relativeAssassinAfin_subset_relativeAssassinAprimeFin :
    relativeAssassinAfin R S N ⊆ relativeAssassinAprimeFin R S N := sorry

/-- Lemma 10.65.1 (5): `A'_fin` is contained in `B_fin`. -/
@[stacks 05GB "(5)"]
theorem relativeAssassinAprimeFin_subset_relativeAssassinBfin :
    relativeAssassinAprimeFin R S N ⊆
      relativeAssassinBfin.{u, v, w, x} R S N := sorry

/-- Lemma 10.65.1 (6): `A` is contained in `B`. -/
@[stacks 05GB "(6)"]
theorem relativeAssassinA_subset_relativeAssassinB :
    relativeAssassin R S N ⊆
      relativeAssassinB.{u, v, w, x} R S N := sorry

/-- Lemma 10.65.1 (7): if `S` is Noetherian, then `A = A_fin`. -/
@[stacks 05GB "(7)"]
theorem relativeAssassinA_eq_relativeAssassinAfin_of_isNoetherianRing
    [IsNoetherianRing S] :
    relativeAssassin R S N = relativeAssassinAfin R S N := sorry

/-- Lemma 10.65.1 (8): if `S` is Noetherian, then `B = B_fin`. -/
@[stacks 05GB "(8)"]
theorem relativeAssassinB_eq_relativeAssassinBfin_of_isNoetherianRing
    [IsNoetherianRing S] :
    relativeAssassinB.{u, v, w, x} R S N =
      relativeAssassinBfin.{u, v, w, x} R S N := sorry

/-- Lemma 10.65.1 (9): if `N` is flat over `R`, then `A = A_fin`. -/
@[stacks 05GB "(9)"]
theorem relativeAssassinA_eq_relativeAssassinAfin_of_flat [Module.Flat R N] :
    relativeAssassin R S N = relativeAssassinAfin R S N := sorry

/-- Lemma 10.65.1 (10): if `N` is flat over `R`, then `A_fin = A'_fin`. -/
@[stacks 05GB "(10)"]
theorem relativeAssassinAfin_eq_relativeAssassinAprimeFin_of_flat [Module.Flat R N] :
    relativeAssassinAfin R S N = relativeAssassinAprimeFin R S N := sorry

/-- Lemma 10.65.1 (11): if `N` is flat over `R`, then `B = B_fin`. -/
@[stacks 05GB "(11)"]
theorem relativeAssassinB_eq_relativeAssassinBfin_of_flat [Module.Flat R N] :
    relativeAssassinB.{u, v, w, x} R S N =
      relativeAssassinBfin.{u, v, w, x} R S N := sorry

/-- Lemma 10.65.1 (12): if `R` is Noetherian and `N` is flat over `R`, then
`A'_fin = B_fin`; together with (1) and (9)--(11), all six source sets are equal. -/
@[stacks 05GB "(12)"]
theorem relativeAssassinAprimeFin_eq_relativeAssassinBfin_of_isNoetherianRing_and_flat
    [IsNoetherianRing R] [Module.Flat R N] :
    relativeAssassinAprimeFin R S N =
      relativeAssassinBfin.{u, v, w, x} R S N := sorry

end Comparisons

#check @relativeAssassinPrimeQuotient
#check @relativeAssassinA_eq_relativeAssassinAprime
#check @relativeAssassinAprimeFin_eq_relativeAssassinBfin_of_isNoetherianRing_and_flat
