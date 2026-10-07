module

public import ReasLib.RingTheory.Flatness.MittagLeffler.Finite
public import ReasLib.RingTheory.Flatness.MittagLeffler.Projective
import StacksCheckRecall

/-!
# Examples of Mittag-Leffler modules

@stack 059R
-/

@[expose] public section

/- Chap10 Example 10 91 1 (1): every finitely presented module is Mittag-Leffler. -/
@[stacks 059R "(1)"]
#check @Module.MittagLeffler.ofFinitePresentation

/- Chap10 Example 10 91 1 (2): every free module is Mittag-Leffler. -/
@[stacks 059R "(2)"]
#check @Module.MittagLeffler.of_free

/- Chap10 Example 10 91 1 (3): every projective module is Mittag-Leffler. -/
@[stacks 059R "(3)"]
#check @Module.MittagLeffler.ofProjective

#check @Module.Finite.mittagLeffler_iff_finitePresentation
