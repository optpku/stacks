module

public import ReasLib.RingTheory.CohenMacaulay.RegularSequence
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Regular sequences pulled back along local homomorphisms

@stack 06LC

This leaf records the maximal regular-sequence consequence of a local map
whose extended maximal ideal has maximal radical.
-/

universe u v

open RingTheory Sequence IsLocalRing

namespace Module.CohenMacaulay

/-- Lemma 10.104.10 (06LC): under a local homomorphism whose extended maximal
ideal has maximal radical, a Cohen--Macaulay target admits a maximal regular
sequence whose entries come from the source. -/
@[stacks 06LC]
theorem exists_regularSequence_map_of_radical_maximalIdeal
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing B]
    [Module.CohenMacaulay B B]
    (φ : A →+* B) [IsLocalHom φ]
    (hrad : maximalIdeal B = (Ideal.map φ (maximalIdeal A)).radical) :
    ∃ fs : List A, fs.length = ringKrullDim B ∧ IsRegular B (fs.map φ) := sorry

end Module.CohenMacaulay
