/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Divisor.Principal
import StacksCheckRecall

open AlgebraicGeometry TopologicalSpace

universe u

/- Lemma 31.26.4 (1): the prime divisors where a function-field unit is not in the image of the
generic-point stalk form a locally finite family. -/
@[stacks 02RL] #check
  (AlgebraicGeometry.Scheme.locallyFinite_primeDivisors_not_mem_genericPointStalk :
    ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X] (f : X.functionFieldˣ),
      LocallyFinite fun Z : PrimeDivisor X ↦
        {x | (f : X.functionField) ∉ X.stalkInFunctionField Z.genericPoint ∧
          x ∈ (Z.support : Set X)})

/- Lemma 31.26.4 (2): the prime divisors where a function-field unit has nonzero order form a
locally finite family. -/
@[stacks 02RL] #check
  (AlgebraicGeometry.Scheme.locallyFinite_primeDivisors_ord_ne_zero :
    ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X] (f : X.functionFieldˣ),
      LocallyFinite fun Z : PrimeDivisor X ↦
        if X.primeDivisorOrder Z f = 0 then
          (∅ : Set X)
        else
          (Z.support : Set X))
