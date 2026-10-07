module

public import ReasLib.RingTheory.Henselian.StrictHenselian.Normal
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 58.12.2 -/
@[stacks 0BSQ]
#check (IsNormalRing.strictHenselianLocalRing :
  (A : Type u) → [CommRing A] → [IsLocalRing A] → [IsNormalRing A] →
    [IsSepClosed (FractionRing A)] → StrictHenselianLocalRing A)
