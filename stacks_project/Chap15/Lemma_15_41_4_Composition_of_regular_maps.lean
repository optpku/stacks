module

public import ReasLib.RingTheory.Regular.Composition
import StacksCheckRecall

/-!
# Lemma 15.41.4 (Composition of regular maps)

@stack 07QI
-/

@[expose] public section

/- Lemma 15.41.4 (Composition of regular maps): regular maps compose when the
fibers of the composite are Noetherian. -/
@[stacks 07QI] #check @RingHom.Regular.comp_of_noetherianFibers

#check @RingHom.Regular.comp
#check @RingHom.Regular.isRegularRing
