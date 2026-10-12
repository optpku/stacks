/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Relative
import StacksCheckRecall

@[expose] public section

/-! @stack 05GC -/

/-!
# Definition 10.65.2

The reusable relative-assassin API lives in
`ReasLib.RingTheory.Ideal.AssociatedPrime.Relative`.
-/

/- Definition 10.65.2 (Tag 05GC): the relative assassin of an `S`-module over `R → S`. -/
@[stacks 05GC]
#check @relativeAssassin

@[stacks 05GC "relative assassin membership"]
#check @mem_relativeAssassin_iff
@[stacks 05GC "fiberwise membership"]
#check @mem_relativeAssassin_iff_fiber
