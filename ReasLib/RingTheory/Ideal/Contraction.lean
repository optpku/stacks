module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Nonzero contraction of ideals

This file gives seven reusable criteria ensuring that every nonzero ideal in a domain extension
has nonzero contraction to the base domain.

@stack 0GS5
-/

@[expose] public section

universe u v

open PrimeSpectrum

namespace Ideal

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]

/-- Lemma 15.108.1 (1): if `B` is a localization of an etale `A`-algebra, every nonzero ideal
of `B` has nonzero contraction to `A`. -/
@[stacks 0GS5 "Lemma 15.108.1 (1)"]
theorem comap_ne_bot_of_localization_etale
    (h : ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
        (_ : IsScalarTower A C B) (M : Submonoid C),
      Algebra.Etale A C ∧ IsLocalization M B)
    (J : Ideal B) (hJ : J ≠ ⊥) :
    J.comap (algebraMap A B) ≠ ⊥ := sorry
-- Proof strategy: use etale and localization flatness to obtain injectivity and a nonempty
-- generic fiber, prove that fiber subsingleton via the etale no-specialization criterion, and
-- apply the unique-generic-fiber contraction argument.

/-- Lemma 15.108.1 (2): if `A → B` is flat and `B` is a localization of an unramified
`A`-algebra, every nonzero ideal of `B` has nonzero contraction to `A`. -/
@[stacks 0GS5 "Lemma 15.108.1 (2)"]
theorem comap_ne_bot_of_flat_localization_unramified [Module.Flat A B]
    (h : ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
        (_ : IsScalarTower A C B) (M : Submonoid C),
      Algebra.Unramified A C ∧ IsLocalization M B)
    (J : Ideal B) (hJ : J ≠ ⊥) :
    J.comap (algebraMap A B) ≠ ⊥ := sorry
-- Proof strategy: flatness supplies injectivity and the generic-fiber point; the localized
-- unramified presentation rules out strict fiber specializations, reducing to the unique
-- generic-fiber case.

/-- Lemma 15.108.1 (3): if `A → B` is flat and `B` is a localization of a quasi-finite
`A`-algebra, every nonzero ideal of `B` has nonzero contraction to `A`. -/
@[stacks 0GS5 "Lemma 15.108.1 (3)"]
theorem comap_ne_bot_of_flat_localization_quasiFinite [Module.Flat A B]
    (h : ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
        (_ : IsScalarTower A C B) (M : Submonoid C),
      Algebra.QuasiFinite A C ∧ IsLocalization M B)
    (J : Ideal B) (hJ : J ≠ ⊥) :
    J.comap (algebraMap A B) ≠ ⊥ := sorry
-- Proof strategy: combine flat injectivity with the quasi-finite fiber antisymmetry theorem to
-- make the generic fiber a singleton, then use the unique-generic-fiber contraction argument.

/-- Lemma 15.108.1 (4): if `A → B` is flat and `B` is a localization of an integral
`A`-algebra, every nonzero ideal of `B` has nonzero contraction to `A`. -/
@[stacks 0GS5 "Lemma 15.108.1 (4)"]
theorem comap_ne_bot_of_flat_localization_integral [Module.Flat A B]
    (h : ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
        (_ : IsScalarTower A C B) (M : Submonoid C),
      Algebra.IsIntegral A C ∧ IsLocalization M B)
    (J : Ideal B) (hJ : J ≠ ⊥) :
    J.comap (algebraMap A B) ≠ ⊥ := sorry
-- Proof strategy: use flatness for the generic point and lying-over/incomparability for the
-- localized integral model to eliminate strict fiber specializations, then invoke the unique
-- generic-fiber endgame.

/-- Lemma 15.108.1 (5): if `A → B` is flat and no fiber contains a nontrivial specialization,
every nonzero ideal of `B` has nonzero contraction to `A`. -/
@[stacks 0GS5 "Lemma 15.108.1 (5)"]
theorem comap_ne_bot_of_flat_fiber_specialization_eq [Module.Flat A B]
    (h : ∀ (p : PrimeSpectrum A) (q q' : p.asIdeal.primesOver B), q ≤ q' → q = q')
    (J : Ideal B) (hJ : J ≠ ⊥) :
    J.comap (algebraMap A B) ≠ ⊥ := sorry
-- Proof strategy: flatness makes `algebraMap A B` injective and places `⊥` in the generic
-- fiber; specialize `h` there to obtain a subsingleton fiber and finish by the generic-fiber
-- contraction argument.

/-- Lemma 15.108.1 (6): if the generic point of `Spec(B)` maps to the generic point of
`Spec(A)` and no fiber contains a nontrivial specialization, every nonzero ideal of `B` has
nonzero contraction to `A`. -/
@[stacks 0GS5 "Lemma 15.108.1 (6)"]
theorem comap_ne_bot_of_genericPoint_fiber_specialization_eq
    (hgeneric : (⊥ : Ideal B).LiesOver (⊥ : Ideal A))
    (h : ∀ (p : PrimeSpectrum A) (q q' : p.asIdeal.primesOver B), q ≤ q' → q = q')
    (J : Ideal B) (hJ : J ≠ ⊥) :
    J.comap (algebraMap A B) ≠ ⊥ := sorry
-- Proof strategy: use `hgeneric` as the generic-fiber witness, apply `h` to show that every
-- point of that fiber equals it, and reduce to the unique-generic-fiber case.

/-- Lemma 15.108.1 (7): if exactly one point of `Spec(B)` lies over the generic point of
`Spec(A)`, every nonzero ideal of `B` has nonzero contraction to `A`. -/
@[stacks 0GS5 "Lemma 15.108.1 (7)"]
theorem comap_ne_bot_of_unique_genericFiber
    (hgeneric : Nonempty ((⊥ : Ideal A).primesOver B) ∧
      Subsingleton ((⊥ : Ideal A).primesOver B))
    (J : Ideal B) (hJ : J ≠ ⊥) :
    J.comap (algebraMap A B) ≠ ⊥ := sorry
-- Proof strategy: if the contraction were `⊥`, localize at the nonzero elements of `A`, choose
-- a prime above the image of `J`, and use uniqueness in the generic fiber to force that prime
-- and hence `J` to be zero.

end Ideal
