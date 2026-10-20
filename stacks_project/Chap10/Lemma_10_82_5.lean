module

public import ReasLib.Algebra.Homology.ShortComplex.UniversallyExact.Flat
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.82.5
@stack 058M
-/

/- Lemma 10.82.5: an `R`-module `M` is flat if and only if every short exact sequence ending in
`M` is universally exact. -/
@[stacks 058M]
#check @Module.Flat.iff_forall_shortExact_universallyExact
