module

public import ReasLib.RingTheory.Smooth.Resolution.GeometricallyRegular
import StacksCheckRecall

@[expose] public section

/- Lemma 16.11.4: resolution at a minimal singular prime over a geometrically
regular algebra is owned by `AlgHom.ResolvableAtPrime`. -/
@[stacks 07FJ]
#check @AlgHom.ResolvableAtPrime.of_minimal
