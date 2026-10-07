module

import StacksCheckRecall
public import ReasLib.RingTheory.Regular.Composition

/-!
# Lemma 15.42.3

@stack 0H7S
-/

@[expose] public section

universe u v

/- Lemma 15.42.3 (0H7S): if `R → S` is a regular ring map, `S` is Noetherian, and `R` is a
regular ring, then `S` is regular. -/
@[stacks 0H7S "regularity ascends along a regular ring map"]
#check fun (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    [IsNoetherianRing S] [IsRegularRing R] (h : (algebraMap R S).Regular) ↦
  (h.isRegularRing : IsRegularRing S)
