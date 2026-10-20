module

public import Mathlib.AlgebraicGeometry.AffineScheme
import StacksCheckRecall

@[expose] public section

/- Lemma 26.11.5: intersecting affine neighbourhoods contain a common standard-open
neighbourhood. -/
@[stacks 01IW] #check AlgebraicGeometry.exists_basicOpen_le_affine_inter
