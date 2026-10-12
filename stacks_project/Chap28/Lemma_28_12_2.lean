/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.SerreCondition.Regular
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 28.12.2: Let `X` be a locally Noetherian scheme. Then `X` is regular if and only if
`X` satisfies `(Rₖ)` for every natural number `k`. -/
@[stacks 0B3C] #check
  (AlgebraicGeometry.Scheme.regular_iff_forall_satisfiesSerreConditionR :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X],
      AlgebraicGeometry.Scheme.Regular X ↔
        ∀ k : ℕ, AlgebraicGeometry.Scheme.satisfiesSerreConditionR X k)
