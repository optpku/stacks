module

import Mathlib.AlgebraicGeometry.Sites.Pretopology
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Stability
import StacksCheckRecall

universe u

/- Lemma 34.6.3: singleton isomorphisms are syntomic coverings; dependent
refinements of syntomic coverings compose to syntomic coverings; and syntomic
coverings remain syntomic coverings after base change along an arbitrary
morphism of schemes. -/
@[stacks 0227] #check
  (AlgebraicGeometry.Scheme.pretopology (@AlgebraicGeometry.Syntomic) :
    CategoryTheory.Pretopology AlgebraicGeometry.Scheme.{u})
