module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition

/-!
# Serre Conditions Along Faithfully Flat Maps

The two ring-level Serre conditions descend along faithfully flat maps.  They
are kept together because their common input and namespace form one coherent
API, while remaining independent of the Chapter 10 proof routes.
-/

@[expose] public section

namespace RingHom.FaithfullyFlat

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] {k : ℕ}

/-- Lemma 10.164.5, tag `0352`: Serre's condition `(S_k)` descends along a
faithfully flat ring homomorphism. -/
@[stacks 0352]
theorem serreConditionS {f : R →+* S} (hff : f.FaithfullyFlat) [SerreConditionS S k] :
    SerreConditionS R k := sorry

/-- Lemma 10.164.6, tag `0353`: Serre's condition `(R_k)` descends along a
faithfully flat ring homomorphism. -/
@[stacks 0353]
theorem serreConditionR {f : R →+* S} (hff : f.FaithfullyFlat) [SerreConditionR S k] :
    SerreConditionR R k := sorry

end RingHom.FaithfullyFlat
