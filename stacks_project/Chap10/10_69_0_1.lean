/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Sequence.QuasiRegular.Basic
import StacksCheckRecall

@[expose] public section

universe u

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]

/-!
# Associated-graded comparison for a finite sequence

The canonical data owner is `QuasiRegular.comparisonMap`; the source equation is recalled directly
so this chapter file does not introduce a second polynomial action, tensor source, or
associated-graded comparison map.

@stack 061N
-/

/- Lemma 10.69.0.1, tag `061N`: the associated-graded equation is the canonical comparison map. -/
@[stacks 061N "associated-graded comparison map"]
#check @QuasiRegular.comparisonMap

/- The surjectivity fact is a reusable companion to the source equation. -/
@[stacks 061N "surjectivity companion"]
#check @QuasiRegular.comparisonMap_surjective

end RingTheory.Sequence

end
