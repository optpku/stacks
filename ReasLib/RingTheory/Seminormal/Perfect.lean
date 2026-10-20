module

public import ReasLib.RingTheory.Seminormal
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.FieldTheory.Perfect
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u

/-- A commutative algebra over the prime field `ZMod p` is absolutely weakly normal if and only
if its `p`-power Frobenius is bijective. -/
@[stacks 0EVV]
theorem absolutelyWeaklyNormalRing_iff_perfectRing
    (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A] [Algebra (ZMod p) A] :
    AbsolutelyWeaklyNormalRing A ↔ PerfectRing A p := sorry
