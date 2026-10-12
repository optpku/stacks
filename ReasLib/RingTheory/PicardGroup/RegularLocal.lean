/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.PicardGroup
public import ReasLib.RingTheory.UniqueFactorizationDomain.RegularLocal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Picard groups of principal localizations of regular local rings

The regular-local UFD instance is the canonical structural input.  This leaf
records its Picard-group consequence for localization away from one element.

@stack 0AFZ
-/

@[expose] public section

universe u

namespace IsRegularLocalRing

/-- Lemma 15.122.1 (0AFZ): the Picard group of `R_f` is trivial when `R` is a
regular local ring. -/
@[stacks 0AFZ "trivial Picard group of a principal localization of a regular local ring"]
theorem subsingletonPicardGroup_localizationAway
    {R : Type u} [CommRing R] [IsRegularLocalRing R] (f : R) :
    Subsingleton (CommRing.Pic (Localization.Away f)) := sorry
-- Proof strategy: synthesize the canonical regular-local
-- `UniqueFactorizationMonoid R` instance, transport unique factorization to
-- `Localization.Away f`, and apply Mathlib's Picard-group subsingleton instance
-- for GCD domains.

end IsRegularLocalRing
