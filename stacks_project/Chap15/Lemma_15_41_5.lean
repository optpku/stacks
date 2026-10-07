module

public import ReasLib.RingTheory.Regular.IndSmooth
import StacksCheckRecall

/-!
Lemma 15.41.5 (07EP): an ind-smooth ring homomorphism with Noetherian fibers is regular.
The canonical theorem is owned by the reusable `RingHom.IndSmooth` API.
@stack 07EP
-/

@[expose] public section

/- Lemma 15.41.5: an ind-smooth ring map with Noetherian fibers is regular. -/
@[stacks 07EP] #check @RingHom.IndSmooth.regular_of_noetherianFibers
