/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.Pi
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.LocalRing.DimensionOne
public import ReasLib.RingTheory.OrderOfVanishing.Power

/-!
# Minimal-prime localizations of one-dimensional local rings

This leaf names the product of minimal-prime localizations, then records power
and integral-image consequences for Noetherian one-dimensional local rings.

@stack 0BWT
@stack 0AB2
@stack 0AB3
@stack 0AB4
-/

@[expose] public section

universe u v

namespace IsLocalRing.DimensionOne.MinimalPrime

/-- The product of the localizations of a ring at all of its minimal primes. -/
@[stacks 0AB2 "product of minimal-prime localizations"]
def localizations (R : Type u) [CommRing R] : Type u :=
  ∀ p : minimalPrimes R, Localization.AtPrime p.1

/-- The product of minimal-prime localizations has its canonical commutative-ring structure. -/
@[stacks 0AB2 "ring structure on the product of minimal-prime localizations", instance]
instance instCommRingLocalizations (R : Type u) [CommRing R] : CommRing (localizations R) :=
  -- Local instance justification (defeq pin): select the raw Pi instance before folding
  -- through `localizations`, avoiding typeclass self-reference.
  letI : CommRing ((p : minimalPrimes R) → Localization.AtPrime p.1) := inferInstance
  this

/-- The product of minimal-prime localizations is canonically an algebra over the base ring. -/
@[stacks 0AB2 "algebra structure on the product of minimal-prime localizations", instance]
instance instAlgebraLocalizations (R : Type u) [CommRing R] : Algebra R (localizations R) :=
  -- Local instance justification (defeq pin): select the raw Pi instance before folding
  -- through `localizations`, avoiding typeclass self-reference.
  letI : Algebra R ((p : minimalPrimes R) → Localization.AtPrime p.1) := inferInstance
  this

/-- Evaluation at a minimal prime from the product of minimal-prime localizations. -/
@[stacks 0AB2 "evaluation from the product of minimal-prime localizations"]
def eval (R : Type u) [CommRing R] (p : minimalPrimes R) :
    localizations R →+* Localization.AtPrime p.1 :=
  Pi.evalRingHom (fun q : minimalPrimes R ↦ Localization.AtPrime q.1) p

/-- Evaluation at a minimal prime computes as function application. -/
@[simp, stacks 0AB2 "minimal-prime localization evaluation"]
theorem eval_apply (R : Type u) [CommRing R] (p : minimalPrimes R) (x : localizations R) :
    eval R p x = x p := sorry
-- Proof strategy: unfold `eval` and `Pi.evalRingHom`; the result is the
-- defining application rule.

/-- Evaluation after the base-ring map is the canonical localization algebra map. -/
@[stacks 0AB2 "evaluation of the diagonal algebra map"]
theorem eval_comp_algebraMap (R : Type u) [CommRing R] (p : minimalPrimes R) :
    (eval R p).comp (algebraMap R (localizations R)) =
      algebraMap R (Localization.AtPrime p.1) := sorry
-- Proof strategy: ext a base-ring element and unfold the product algebra map
-- and `eval`; both sides are the canonical localization map at `p`.

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- In a Noetherian one-dimensional local ring, two maximal-ideal elements with the same image
in the product of minimal-prime localizations have equal positive powers. -/
@[stacks 0AB2]
theorem exists_pow_eq_of_equal_localizations
    (hdim : ringKrullDim R = 1)
    {a₁ a₂ : R} (ha₁ : a₁ ∈ maximalIdeal R) (ha₂ : a₂ ∈ maximalIdeal R)
    (hL : algebraMap R (localizations R) a₁ = algebraMap R (localizations R) a₂) :
    ∃ n : ℕ, 0 < n ∧ a₁ ^ n = a₂ ^ n := sorry
-- Proof strategy: equality in every minimal-prime localization places
-- `a₁ - a₂` in the kernel of the reduced diagonal map.  In the Noetherian
-- one-dimensional local setting that kernel is killed by a power of the
-- maximal ideal.  Expand `a₁ ^ n - a₂ ^ n` as `(a₁ - a₂)` times a sum lying in
-- a sufficiently high maximal-ideal power.

/-- In a Noetherian one-dimensional local ring, a sum of an image of a maximal-ideal element and
an element of the extended nilradical has a positive power in the image of the ring in the
product of minimal-prime localizations. -/
@[stacks 0AB3]
theorem exists_pow_mem_range_of_maximalIdeal_add_intersection
    (hdim : ringKrullDim R = 1) {a : R} {i f : localizations R}
    (ha : a ∈ maximalIdeal R)
    (hi : i ∈ Ideal.map (algebraMap R (localizations R)) (nilradical R))
    (hf : f = i + algebraMap R (localizations R) a) :
    ∃ n : ℕ, 0 < n ∧ f ^ n ∈ (algebraMap R (localizations R)).range := sorry
-- Proof strategy: elements coming from `nilradical R` lie in the
-- maximal-ideal-power torsion of the reduced diagonal cokernel.  Choose a
-- common annihilating power and expand the power of `i + algebraMap _ _ a`;
-- all terms involving `i` vanish modulo the diagonal image, leaving the image
-- of a power of `a`.

/-- An integral map into the product of minimal-prime localizations of a Noetherian
one-dimensional local ring has an image element from the maximal ideal whose principal radical
is maximal. -/
@[stacks 0AB4]
theorem exists_sameImage_integralSourceElem
    (hdim : ringKrullDim R = 1) {K : Type v} [CommRing K]
    (f : K →+* localizations R) (hInt : f.IsIntegral) :
    ∃ a : maximalIdeal R, ∃ x : K,
      algebraMap R (localizations R) a = f x ∧
        maximalIdeal R = (Ideal.span ({(a : R)} : Set R)).radical := sorry
-- Proof strategy: apply lying-over to the integral map and the coordinate
-- primes of `localizations R`, then use one-dimensional locality to choose an
-- image element avoiding all minimal primes.  Its contraction lies in the
-- maximal ideal but in no minimal prime, so the principal ideal has maximal
-- radical; package the source element of `K` giving the same product image.

/-- The number of minimal primes of a one-dimensional Noetherian local ring is at most the order
of a maximal-ideal element that avoids every minimal prime. -/
@[stacks 0BWT "Lemma 15.126.2, minimal-prime count bounded by principal quotient length"]
theorem encard_le_ord
    (hdim : ringKrullDim R = 1) (x : maximalIdeal R)
    (hx : ∀ p : minimalPrimes R, (x : R) ∉ p.1) :
    (minimalPrimes R).encard ≤ Ring.ord R x := sorry
-- Proof strategy: compare the reduced diagonal map with the product over all
-- minimal primes.  After quotienting by powers of `x`, each minimal-prime
-- coordinate contributes at least that exponent to the product length, while
-- the diagonal cokernel is killed by a fixed power of `x`.  The upper bound is
-- `Ring.ord_pow_le`; cancel the exponent in the resulting asymptotic inequality
-- to obtain the stated extended-cardinality bound.

end IsLocalRing.DimensionOne.MinimalPrime
