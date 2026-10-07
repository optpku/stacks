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
