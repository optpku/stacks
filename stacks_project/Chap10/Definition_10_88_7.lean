module

public import ReasLib.RingTheory.Flatness.MittagLeffler
public import ReasLib.RingTheory.Flatness.MittagLeffler.Properties
import StacksCheckRecall

@[expose] public section

/-!
# Mittag-Leffler modules

Definition 10.88.7: an `R`-module `M` is Mittag-Leffler if the equivalent
conditions of Proposition 10.88.6 hold.  In particular a finitely presented
module is Mittag-Leffler.

The reusable owner is the unbundled property class `Module.MittagLeffler`,
witnessed by a concrete `Module.MittagLeffler.Presentation`.

@stack 059F
-/

/- Definition 10.88.7: an `R`-module is Mittag-Leffler when the equivalent
conditions of Proposition 10.88.6 hold. -/
@[stacks 059F]
#check @Module.MittagLeffler
@[stacks 059F]
#check @Module.MittagLeffler.Presentation
@[stacks 059F]
#check @Module.MittagLeffler.Presentation.toMittagLeffler
@[stacks 059F]
#check @Module.MittagLeffler.ofFinitePresentation
