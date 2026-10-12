/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import ReasLib.RingTheory.Sequence.Regularity
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Localization of regular sequences

Regularity over the localization at a prime spreads to a principal open
containing that prime for finite modules over Noetherian rings.
-/

universe u v

namespace RingTheory.Sequence.IsRegular

/-- A sequence regular after localization at a prime is regular over some
principal open containing that prime. -/
@[stacks 061L]
theorem exists_away_of_atPrime
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : Ideal R) [p.IsPrime] {xs : List R}
    (hxs : IsRegular (LocalizedModule.AtPrime p M)
      (xs.map (algebraMap R (Localization.AtPrime p)))) :
    ∃ g : R, g ∉ p ∧
      IsRegular (LocalizedModule.Away g M)
        (xs.map (algebraMap R (Localization.Away g))) := sorry

end RingTheory.Sequence.IsRegular
