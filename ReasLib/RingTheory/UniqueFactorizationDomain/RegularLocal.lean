/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RegularLocalRing.Domain
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import Mathlib.Tactic.CrossRefAttribute

/-!
# Unique factorization in regular local rings

Every regular local ring is a unique-factorization monoid.
-/

@[expose] public section

universe u

namespace IsRegularLocalRing

variable {R : Type u} [CommRing R]

/-- A regular local ring is a unique-factorization monoid. -/
@[stacks 0AG0 "Lemma 15.122.2: regular local rings are UFDs"]
instance uniqueFactorizationMonoid [IsRegularLocalRing R] :
    UniqueFactorizationMonoid R := sorry
-- Proof strategy: induct on `ringKrullDim R`.  In positive dimension choose a
-- regular parameter `x ∈ maximalIdeal R \ maximalIdeal R ^ 2` with prime
-- principal ideal, prove the away localization `Rₓ` is factorial from the
-- smaller-dimensional regular local stalks, and apply Nagata's criterion to
-- conclude that every height-one prime of `R` is principal.

end IsRegularLocalRing

end
