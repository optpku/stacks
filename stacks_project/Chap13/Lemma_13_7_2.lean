module

import ReasLib.CategoryTheory.Adjunction.ZeroKernel
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.7.2

The reusable owner separates the counit, essential-surjectivity, and equivalence consequences of
the zero-kernel hypothesis on a right adjoint.
-/

@[stacks 09J1 "counit components"] #check @CategoryTheory.Adjunction.ZeroKernel.counit_isIso

@[stacks 09J1 "essential surjectivity"] #check @CategoryTheory.Adjunction.ZeroKernel.essSurj

@[stacks 09J1] #check @CategoryTheory.Adjunction.ZeroKernel.isEquivalence
