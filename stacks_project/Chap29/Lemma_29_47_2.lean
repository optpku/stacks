module

import StacksCheckRecall
import ReasLib.RingTheory.Seminormal

universe u

/- Lemma 29.47.2 (1): Seminormality is a local property of commutative rings. -/
@[stacks 0EUM] #check (SeminormalRing.ringPropertyIsLocal :
  RingPropertyIsLocal (fun A : CommRingCat.{u} ↦ SeminormalRing A))

/- Lemma 29.47.2 (2): Absolute weak normality is a local property of commutative rings. -/
@[stacks 0EUM] #check (AbsolutelyWeaklyNormalRing.ringPropertyIsLocal :
  RingPropertyIsLocal (fun A : CommRingCat.{u} ↦ AbsolutelyWeaklyNormalRing A))
