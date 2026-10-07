module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Duality.TorAmplitude
import StacksCheckRecall

/-!
# Remark 15.75.16 (0H81)

If `K` is perfect with Tor-amplitude `[a, b]`, its derived dual has Tor-amplitude
`[-b, -a]`.  The source-facing statement is owned by the narrow perfect-duality
Tor-amplitude leaf; no second `derivedDual` or projective-amplitude stack is introduced here.

@stack 0H81
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.DerivedCategory.Perfect

namespace CategoryTheory.DerivedCategory.Perfect.Duality

@[stacks 0H81 "Remark 15.75.16: Tor-amplitude of the perfect derived dual"]
#check @dual_hasTorAmplitudeIn_neg_swap

end CategoryTheory.DerivedCategory.Perfect.Duality

end
