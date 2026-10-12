/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Henselian
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Henselian adic completions

@stack 0A1W

The maximal-ideal completion of a Noetherian local ring is complete for its
own maximal ideal and hence is a henselian local ring. This file registers the
result as the canonical global instance expected by lifting APIs.
-/

@[expose] public section

open IsLocalRing

universe u

namespace AdicCompletion

variable {R : Type u} [CommRing R]

/-- The completion of a local ring along its finitely generated maximal ideal
is henselian local. -/
@[stacks 0A1W "henselian completion at a finitely generated maximal ideal"]
theorem henselianLocalRing_of_fg [IsLocalRing R]
    (hfg : (maximalIdeal R).FG) :
    HenselianLocalRing (AdicCompletion (maximalIdeal R) R) := sorry

/-- The maximal-ideal completion of a Noetherian local ring is henselian
local. This is the canonical typeclass specialization of
`henselianLocalRing_of_fg`. -/
@[stacks 0A1W "henselian maximal-ideal completion"]
instance instHenselianLocalRing [IsNoetherianRing R] [IsLocalRing R] :
    HenselianLocalRing (AdicCompletion (maximalIdeal R) R) := sorry

end AdicCompletion
