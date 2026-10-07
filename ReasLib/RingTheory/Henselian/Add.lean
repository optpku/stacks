module

public import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sums of henselian ideals

@stack 0G1R

The sum of two henselian ideals in a commutative ring is henselian.
-/

@[expose] public section

universe u

variable {A : Type u} [CommRing A]

/-- Lemma 15.11.10 (Stacks `0G1R`): if `(A, I)` and `(A, I')` are henselian pairs, then
`(A, I + I')` is a henselian pair. -/
@[stacks 0G1R]
instance ideal_add_henselianRing (I I' : Ideal A)
    [HenselianRing A I] [HenselianRing A I'] :
    HenselianRing A (I + I') := sorry
