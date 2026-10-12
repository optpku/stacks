/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Completion.LocalRing

@[expose] public section

/-!
# Noetherian Complete Local Rings

This leaf records the finite-maximal-ideal criterion for a complete local ring
to be Noetherian.

@stack 032B
-/

universe u

open IsLocalRing

namespace IsCompleteLocalRing

/-- Lemma 10.160.3, tag `032B`: a complete local ring with finitely generated
maximal ideal is Noetherian. -/
@[stacks 032B]
theorem isNoetherianRing_of_maximalIdeal_fg
    {R : Type u} [CommRing R] [IsCompleteLocalRing R]
    (hfg : (maximalIdeal R).FG) : IsNoetherianRing R := sorry

end IsCompleteLocalRing
