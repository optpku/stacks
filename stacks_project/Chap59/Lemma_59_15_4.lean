module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Pretopology

@[expose] public section

universe u

/- Lemma 59.15.4: the collection of fpqc coverings on schemes satisfies the
axioms of a site, represented by the canonical fpqc pretopology. -/
@[stacks 03NZ] #check
  (AlgebraicGeometry.Scheme.fpqcPretopology :
    CategoryTheory.Pretopology AlgebraicGeometry.Scheme.{u})
