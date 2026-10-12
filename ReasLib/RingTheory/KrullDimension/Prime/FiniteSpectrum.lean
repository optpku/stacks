/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.KrullDimension.Prime
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Noetherian rings with finite prime spectrum

A Noetherian ring whose prime spectrum is finite has Krull dimension at most
one.
-/

universe u

namespace Ring

/-- A Noetherian ring with finite prime spectrum has Krull dimension at most
one, available to typeclass search. -/
@[stacks 0ALV "canonical dimension bound"]
instance krullDimLEOne_of_finitePrimeSpectrum
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    [Finite (PrimeSpectrum R)] : KrullDimLE 1 R := sorry

/-- A Noetherian ring with finitely many prime ideals
has Krull dimension at most one. -/
@[stacks 0ALV]
theorem krullDim_le_one_of_finitePrimeSpectrum
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    [Finite (PrimeSpectrum R)] : ringKrullDim R ≤ 1 := sorry

end Ring
