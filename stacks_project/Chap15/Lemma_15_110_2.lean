module

import StacksCheckRecall
public import ReasLib.RingTheory.Catenary.Formal.Universal

/-!
@stack 0AW3
-/

@[expose] public section

universe u

/- Lemma 15.110.2 (current Stacks numbering: Lemma 15.111.2, tag `0AW3`):
if a Noetherian local ring is not formally catenary, then it is not universally
catenary. -/
@[stacks 0AW3 "Lemma 15.110.2"]
#check fun (A : Type u) [CommRing A] [IsLocalRing A]
    (hA : ¬ IsFormallyCatenaryRing A) ↦
  (IsFormallyCatenaryRing.not_universally (A := A) hA :
    ¬ UniversallyCatenaryRing A)
