module

public import ReasLib.RingTheory.Catenary.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Prime chains in catenary spectra

`IsCatenaryRing` remains the ring-level owner.  This leaf exposes the
prime-interval views used by commutative-algebra arguments, without storing a
second catenary structure or a private prime/irreducible-closed equivalence.
-/

universe u

open Set Order

namespace IsCatenaryRing

variable {R : Type u} [CommRing R] [IsCatenaryRing R]

/-- In a catenary ring, every finite chain in a comparable prime interval has
a common natural-number bound. -/
@[stacks 00NI "bounded finite prime chains"]
theorem primeChainsBounded (p q : PrimeSpectrum R) (hpq : p ≤ q) :
    ∃ n : ℕ, ∀ s : Set (Set.Icc p q),
      IsChain (· ≤ ·) s → s.Finite → s.encard ≤ n + 1 := sorry
/- Proof strategy: transport the interval to irreducible closed subsets using
`PrimeSpectrum.pointsEquivIrreducibleCloseds`, then use the finite-codimension
field of `TopologicalSpace.CatenarySpace` and the flag bound. -/

/-- In a catenary ring, maximal prime chains in a fixed comparable interval
have the same cardinality. -/
@[stacks 00NI "equal lengths of maximal prime chains"]
theorem maximalPrimeChainsHaveSameLength
    (p q : PrimeSpectrum R) (hpq : p ≤ q)
    {s t : Set (Set.Icc p q)}
    (hs : IsMaxChain (· ≤ ·) s) (ht : IsMaxChain (· ≤ ·) t) :
    s.encard = t.encard := sorry
/- Proof strategy: transport both maximal chains to the irreducible-closed
interval and apply `CatenarySpace.maximalIrreducibleClosedChainsHaveLength`. -/

end IsCatenaryRing

/-- A Noetherian commutative ring is catenary if and only if relative prime heights
are additive along every nested triple of prime ideals. -/
theorem isCatenaryRing_iff_height_additive {A : Type u} [CommRing A] [IsNoetherianRing A] :
    IsCatenaryRing A ↔
      ∀ ⦃p₁ p₂ p₃ : PrimeSpectrum A⦄, p₁ ≤ p₂ → p₂ ≤ p₃ →
        (p₃.asIdeal.map (Ideal.Quotient.mk p₁.asIdeal)).height =
          (p₃.asIdeal.map (Ideal.Quotient.mk p₂.asIdeal)).height +
            (p₂.asIdeal.map (Ideal.Quotient.mk p₁.asIdeal)).height := sorry
