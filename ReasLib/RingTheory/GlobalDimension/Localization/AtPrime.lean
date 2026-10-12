/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.GlobalDimension.IdealQuotient
public import ReasLib.RingTheory.GlobalDimension.Localization

/-!
# Detecting global dimension on localizations

For a commutative Noetherian ring, a fixed global-dimension bound can be checked after
localization at every maximal or prime ideal. Taking an existential uniform bound gives the
corresponding criteria for finite global dimension.
-/

@[expose] public section

open CategoryTheory

universe u

namespace HasGlobalDimensionLE

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- A fixed global-dimension bound on a commutative Noetherian ring is detected at all maximal
localizations. -/
@[stacks 00O9 "fixed bound at maximal ideals"]
theorem iff_forall_atMaximal (n : ℕ) :
    HasGlobalDimensionLE R n ↔
      ∀ m : MaximalSpectrum R,
        HasGlobalDimensionLE (Localization.AtPrime m.asIdeal) n := sorry

/-- A fixed global-dimension bound on a commutative Noetherian ring is detected at all prime
localizations. -/
@[stacks 00O9 "fixed bound at prime ideals"]
theorem iff_forall_atPrime (n : ℕ) :
    HasGlobalDimensionLE R n ↔
      ∀ p : PrimeSpectrum R,
        HasGlobalDimensionLE (Localization.AtPrime p.asIdeal) n := sorry

end HasGlobalDimensionLE

namespace IsFiniteGlobalDimensionRing

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Lemma 10.110.2 (Stacks `00O9`): a commutative Noetherian ring has finite global dimension
exactly when its maximal localizations have one uniform global-dimension bound. -/
@[stacks 00O9]
theorem iff_exists_uniform_atMaximal :
    IsFiniteGlobalDimensionRing R ↔
      ∃ n : ℕ, ∀ m : MaximalSpectrum R,
        HasGlobalDimensionLE (Localization.AtPrime m.asIdeal) n := sorry

/-- Finite global dimension of a commutative Noetherian ring is equivalently detected by one
uniform bound on all prime localizations. -/
@[stacks 00O9 "prime form"]
theorem iff_exists_uniform_atPrime :
    IsFiniteGlobalDimensionRing R ↔
      ∃ n : ℕ, ∀ p : PrimeSpectrum R,
        HasGlobalDimensionLE (Localization.AtPrime p.asIdeal) n := sorry

end IsFiniteGlobalDimensionRing
