module

public import ReasLib.RingTheory.Henselian.Add
import StacksCheckRecall

/-!
# Lemma 15.11.10

@stack 0G1R
-/

@[expose] public section

universe u

variable {A : Type u} [CommRing A]
variable (I I' : Ideal A) [HenselianRing A I] [HenselianRing A I']

-- Lemma 15.11.10 (0G1R): the sum of two henselian ideals is henselian.
@[stacks 0G1R]
#check (inferInstance : HenselianRing A (I + I'))

#check @ideal_add_henselianRing
