/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Nagata

@[expose] public section

/-!
# Characterizations of Nagata rings

This module collects the reusable equivalence between the intrinsic Nagata
condition, finite-type stability, and the universally Japanese Noetherian
formulation.
-/

universe u v

namespace NagataRing

variable {R : Type u} [CommRing R]

/-- For a commutative ring `R`, the following are equivalent: `R` is Nagata,
every finite type `R`-algebra is Nagata, and `R` is universally Japanese and
Noetherian. -/
@[stacks 0334]
theorem tfae :
    List.TFAE
      [ NagataRing R,
        ∀ (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S], NagataRing S,
        UniversallyJapaneseRing R ∧ IsNoetherianRing R ] := sorry

/-- The Nagata condition is equivalent to being universally Japanese and
Noetherian. -/
theorem iff_universallyJapanese_noetherian :
    NagataRing R ↔ UniversallyJapaneseRing.{u, v} R ∧ IsNoetherianRing R := sorry

/-- Every Nagata ring is universally Japanese. -/
instance toUniversallyJapanese (R : Type u) [CommRing R] [NagataRing R] :
    UniversallyJapaneseRing.{u, v} R := sorry

end NagataRing
