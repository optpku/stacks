module

public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.ShortExact
public import ReasLib.CategoryTheory.Subobject.Kernel
import StacksCheckRecall

/-!
# Lemma 12.31.6

Compatibility entry point for Mittag-Leffler transfer along short exact inverse-system rows.
The reusable APIs are owned by the corresponding neutral ReasLib leaves.
-/

@[expose] public section

namespace CategoryTheory

/- Lemma 12.31.6: the middle and left towers of a short exact row are Mittag-Leffler
simultaneously when the quotient tower is essentially constant. -/
@[stacks 070D]
#check @ShortComplex.ShortExact.MittagLeffler.Right.left_iff_middle_of_essentiallyConstant

#check @SequentialInverseSystem.transitionMap_comp
#check @SequentialInverseSystem.IsMittagLeffler.shift_iff
#check @PreorderInverseSystem.Transition.EventuallyZero
#check @NatTrans.shift
#check @SequentialInverseSystem.shiftNatTrans_app
#check @SequentialInverseSystem.ShortComplex.ShortExact.app
#check @ShortComplex.ShortExact.MittagLeffler.Right.left_iff_middle_of_eventuallyZero
#check @ShortComplex.ShortExact.MittagLeffler.Right.left_iff_middle_of_constant

end CategoryTheory
