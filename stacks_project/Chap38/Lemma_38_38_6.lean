module

public import ReasLib.RingTheory.Seminormal.Perfect
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 38.38.6: for a prime `p`, a commutative `ZMod p`-algebra `A` is
absolutely weakly normal if and only if it is perfect. -/
@[stacks 0EVV]
#check (absolutelyWeaklyNormalRing_iff_perfectRing :
  ∀ (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A] [Algebra (ZMod p) A],
    AbsolutelyWeaklyNormalRing A ↔ PerfectRing A p)
