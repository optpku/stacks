/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flatness.MittagLeffler.Projective
import StacksCheckRecall

@[expose] public section

/-!
# Theorem 10.93.3

@stack 059Z
-/

/- Chap10 Theorem 10 93 3: projective modules are exactly the flat Mittag-Leffler modules that
are direct sums of countably generated submodules. -/
@[stacks 059Z]
#check @Module.Projective.iff_flat_mittagLeffler_directSum
