module

public import ReasLib.AlgebraicGeometry.Scheme.Immersion
import StacksCheckRecall

@[expose] public section

/- Lemma 26.10.4: an immersion is closed exactly when its set-theoretic image is closed. -/
@[stacks 01IQ] #check
  AlgebraicGeometry.Scheme.Hom.isClosedImmersion_iff_isClosed_range_of_isImmersion
