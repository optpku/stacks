/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.IntegralClosure
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Prime fibers of integral closures over henselian local rings

An integral closure in a field is henselian local, so the prime fiber over the source maximal
ideal consists of the target maximal ideal.

@stack 09E8
-/

open Ideal IsLocalRing

universe u v

namespace integralClosure.Henselian

/-- Remark 15.112.6 (4): the integral closure of a henselian local ring in a field has a unique
prime above the source maximal ideal. -/
@[stacks 09E8 "henselian integral-closure prime fiber"]
theorem primesOver_eq_singleton
    {A : Type u} {L : Type v}
    [CommRing A] [Field L] [Algebra A L] [HenselianLocalRing A] :
    (maximalIdeal A).primesOver (integralClosure A L) =
      ({maximalIdeal (integralClosure A L)} : Set (Ideal (integralClosure A L))) := sorry
-- Proof strategy: use the canonical `HenselianLocalRing` instance on `integralClosure A L` and
-- locality of the integral algebra map; show every prime over `maximalIdeal A` is maximal, hence
-- equals the unique maximal ideal of the target, and prove that target maximal ideal lies over the
-- source maximal ideal before applying `Set.eq_singleton_iff_unique_mem`.

end integralClosure.Henselian
