/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Flatness of adic completion

Mathlib already owns Noetherian adic-completion flatness through the instance
`AdicCompletion.flat_of_isNoetherian`, and exactness through
`AdicCompletion.map_exact`. This leaf retains only the root-level compatibility
entry required by older consumers.
@stack 0BNP
-/

universe u

/-- Compatibility bridge for the former root-level flatness theorem. New code
should use `AdicCompletion.flat_of_isNoetherian` through typeclass search. -/
@[stacks 00MB "compatibility",
  stacks 0BNP "Noetherian adic completion is flat"]
theorem adicCompletion_algebraMap_flat
    {R : Type u} [CommRing R] (I : Ideal R) [IsNoetherianRing R] :
    (algebraMap R (AdicCompletion I R)).Flat := sorry
