/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.AlgebraicGeometry.Sites.BigZariski
import StacksCheckRecall

universe u

/- Lemma 34.3.2: Zariski coverings of schemes contain singleton isomorphisms, compose under
refinement, and are stable under base change. -/
@[stacks 020P] #check (AlgebraicGeometry.Scheme.zariskiPretopology.{u} :
  CategoryTheory.Pretopology AlgebraicGeometry.Scheme.{u})
