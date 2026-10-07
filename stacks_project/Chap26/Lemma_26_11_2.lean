module

public import Mathlib.AlgebraicGeometry.AffineScheme
import StacksCheckRecall

@[expose] public section

/- Lemma 26.11.2: affine opens form a basis for the topology of a scheme. -/
@[stacks 01IT] #check AlgebraicGeometry.Scheme.isBasis_affineOpens
