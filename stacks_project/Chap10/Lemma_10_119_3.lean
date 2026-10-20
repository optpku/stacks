module

public import ReasLib.RingTheory.LocalRing.Kollar.DimensionOne
import StacksCheckRecall

/-!
# Exceptional Extensions in Embedding Dimension Greater Than One

The one-dimensional case of Kollár's criterion produces an exceptional finite extension when the
cotangent space has dimension greater than one.

@stack 00P9
-/

/- Lemma 10.119.3: a one-dimensional Noetherian local ring whose cotangent
space has dimension greater than one admits an exceptional finite extension. -/
@[stacks 00P9]
#check @IsLocalRing.Kollar.hasExceptionalExtension_of_embeddingDimension_gt_one

/- The owner predicate retains the finite algebra, non-bijectivity,
maximal-ideal-power torsion, and associated-prime clauses as reusable data. -/
#check @IsLocalRing.Kollar.HasExceptionalExtension.spec
