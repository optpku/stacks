/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Ideals after principal localization

This leaf records the ideal-theoretic criterion for an ideal to become the
unit ideal after localizing away from one element, together with the prime
carrier used by relative product localizations.

@stack 0H7N
@stack 077H
-/

@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [CommSemiring R]

/-- Stacks 0H7N: an ideal becomes the unit ideal after localizing away from
`f` exactly when it contains a power of `f`. -/
@[stacks 0H7N "principal-localization ideal criterion"]
theorem map_away_eq_top_iff (f : R) (J : Ideal R) :
    J.map (algebraMap R (Localization.Away f)) = ⊤ ↔ ∃ n : ℕ, f ^ n ∈ J := sorry

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The prime carrier in `Localization.Away ((algebraMap R S f) * g)` obtained by mapping
`q : Ideal S` along the canonical localization map. -/
@[stacks 077H "localized prime carrier"]
def mapAwayMul (q : Ideal S) (f : R) (g : S) :
    Ideal (Localization.Away ((algebraMap R S f) * g)) :=
  q.map (algebraMap S (Localization.Away ((algebraMap R S f) * g)))

/-- Mapping a prime away from two avoided factors gives a prime ideal in the product
localization. -/
@[stacks 077H "localized prime"]
theorem mapAwayMul_isPrime (q : Ideal S) [q.IsPrime] (f : R) (g : S)
    (hf : f ∉ q.comap (algebraMap R S)) (hg : g ∉ q) :
    (q.mapAwayMul f g).IsPrime := sorry

/-- Source-facing prime bridge for a prime `q` lying over `p`; the generic version only needs
the contracted-prime condition `f ∉ q.comap (algebraMap R S)`. -/
@[stacks 077H "localized prime over a base prime"]
theorem mapAwayMul_isPrime_of_liesOver
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (f : R) (g : S) (hf : f ∉ p) (hg : g ∉ q) :
    (q.mapAwayMul f g).IsPrime := sorry

/-- The product-localization prime contracts to its original prime. -/
@[stacks 077H "localized prime contraction"]
theorem comap_mapAwayMul (q : Ideal S) [q.IsPrime] (f : R) (g : S)
    (hf : f ∉ q.comap (algebraMap R S)) (hg : g ∉ q) :
    (q.mapAwayMul f g).comap
        (algebraMap S (Localization.Away ((algebraMap R S f) * g))) = q := sorry

/-- The product-localization prime lies over the original prime.  This remains a theorem rather
than a global instance because the construction requires the avoidance hypotheses `hf` and `hg`. -/
@[stacks 077H "localized prime lies over its source"]
theorem mapAwayMul_liesOver (q : Ideal S) [q.IsPrime] (f : R) (g : S)
    (hf : f ∉ q.comap (algebraMap R S)) (hg : g ∉ q) :
    (q.mapAwayMul f g).LiesOver q := sorry

end Ideal
