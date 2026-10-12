/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Catenary.Universally
import StacksCheckRecall

/-!
# Definition 10.105.3

@stack 00NL

`UniversallyCatenaryRing` is the reusable commutative-algebra owner in
`ReasLib.RingTheory.Catenary.Universally`.
-/

/- Definition 10.105.3: a Noetherian ring is universally catenary when every finite type
algebra over it is catenary. -/
@[stacks 00NL]
#check @UniversallyCatenaryRing
