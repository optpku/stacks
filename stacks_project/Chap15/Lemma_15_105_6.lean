module

public import ReasLib.RingTheory.AbsolutelyFlat.Pi
import StacksCheckRecall

/-!
Lemma 15.105.6 (092G): a product of fields is an absolutely flat ring.

@stack 092G
-/

@[expose] public section

universe u v

section

variable {ι : Type u} (K : ι → Type v) [∀ i, Field (K i)]

/- Lemma 15.105.6 (092G), as the field specialization of the canonical product instance. -/
@[stacks 092G]
#check
  (isAbsolutelyFlatRing_pi (K := K) : IsAbsolutelyFlatRing ((i : ι) → K i))

#check @IsAbsolutelyFlatRing.instPi

end
