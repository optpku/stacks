/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Flat.Stability
public import ReasLib.Algebra.Module.CountablyGenerated.BaseChange
public import ReasLib.RingTheory.Flatness.MittagLeffler.BaseChange
import StacksCheckRecall

/-!
# Ascending module properties

@stack 05A3
-/

@[expose] public section

/- Chap10 Lemma 10 94 1 (1): flatness is preserved by extension of scalars. -/
@[stacks 05A3 "(1)"]
#check Module.Flat.baseChange

/- Chap10 Lemma 10 94 1 (2): the Mittag-Leffler property is preserved by extension of scalars. -/
@[stacks 05A3 "(2)"]
#check Module.MittagLeffler.baseChange

/- Chap10 Lemma 10 94 1 (3): extension of scalars preserves decompositions into countably
generated submodules. -/
@[stacks 05A3 "(3)"]
#check Module.CountablyGenerated.IsDirectSum.baseChange

/- Chap10 Lemma 10 94 1 (4): projectivity is preserved by extension of scalars. -/
@[stacks 05A3 "(4)"]
#check Module.Projective.tensorProduct

#check @Module.CountablyGenerated.baseChange
#check @Module.IsDirectSumOfCountablyGenerated.baseChange
