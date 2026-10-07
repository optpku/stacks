module

public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Transport
import StacksCheckRecall

/-!
# Lemma 10.70.8 transport recall

The generic transport API is owned by `HomogeneousLocalization.Transport`.
No chapter-local aliases are retained.
-/

@[expose] public section

/- Lemma 10.70.8 (0BBI): recall the homogeneous-localization transport used
by the principal scaling construction. -/
@[stacks 0BBI] #check @HomogeneousLocalization.Transport.awayMap_fromZeroRingHom
#check @HomogeneousLocalization.Transport.cast_away_val
