/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap33.Lemma_33_38_6

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 33.38.10: every Noetherian reduced separated scheme of dimension `1` has an ample
invertible sheaf. -/
@[stacks 09NX] #check
  (AlgebraicGeometry.Scheme.Modules.hasAmpleInvertibleModule_of_reduced_dimension_one :
    ∀ {X : Scheme.{u}} [IsNoetherian X] [IsReduced X] [X.IsSeparated],
      topologicalKrullDim X = 1 →
        AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule X)
