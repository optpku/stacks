module

import Mathlib.AlgebraicGeometry.Sites.BigZariski
import StacksCheckRecall

universe u

/- Lemma 34.3.2: Zariski coverings of schemes contain singleton isomorphisms, compose under
refinement, and are stable under base change. -/
@[stacks 020P] #check (AlgebraicGeometry.Scheme.zariskiPretopology.{u} :
  CategoryTheory.Pretopology AlgebraicGeometry.Scheme.{u})
