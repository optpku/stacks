/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.InverseLimit
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.11.3

The sequential transition-kernel and limit-projection results are owned by
`ReasLib.RingTheory.Henselian.InverseLimit` using the system-level surjectivity and
local-nilpotence predicates.

@stack 0CT7
-/

/- Lemma 15.11.3: locally nilpotent successor kernels remain locally nilpotent along every long
transition. -/
@[stacks 0CT7 "locally nilpotent long transition kernels"]
#check @CategoryTheory.SequentialInverseSystem.transitionMap_ker_isLocallyNilpotent

/- Lemma 15.11.3: under surjectivity, every limit-projection kernel defines a henselian pair. -/
@[stacks 0CT7 "henselian kernel of a sequential limit projection"]
#check @CategoryTheory.SequentialInverseSystem.limitProjection_ker_henselianRing

end
