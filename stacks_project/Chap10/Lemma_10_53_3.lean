/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Artinian.Module
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.53.3

@stack 00J7
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {R : Type u} [CommRing R] [IsArtinianRing R]

/- Lemma 10.53.3: if `R` is Artinian, then `R` has only finitely many maximal ideals. The owner
abstraction is `IsArtinianRing R`, and the source-facing conclusion is the derived instance
`Finite (MaximalSpectrum R)` provided by `IsArtinianRing.instFiniteMaximalSpectrum`. -/
@[stacks 00J7]
#check @IsArtinianRing.instFiniteMaximalSpectrum
