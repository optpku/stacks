/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.SerreCondition
import StacksCheckRecall

/-!
# Definition 28.12.1

Serre's conditions `(R_k)` and `(S_k)` for locally Noetherian schemes.

@stack 033Q
-/

@[expose] public section

open AlgebraicGeometry
open scoped ENat

universe u

variable (X : Scheme.{u}) [IsLocallyNoetherian X] (k : ℕ)

/- Definition 28.12.1: a locally Noetherian scheme satisfies `(R_k)` when every stalk of
Krull dimension at most `k` is a regular local ring. -/
@[stacks 033Q] #check
  (AlgebraicGeometry.Scheme.satisfiesSerreConditionR_iff X k :
    AlgebraicGeometry.Scheme.satisfiesSerreConditionR X k ↔
      ∀ x : X,
        ringKrullDim (X.presheaf.stalk x) ≤ k →
          IsRegularLocalRing (X.presheaf.stalk x))

#check
  (AlgebraicGeometry.Scheme.satisfiesSerreConditionS_iff_ringKrullDim X k :
    AlgebraicGeometry.Scheme.satisfiesSerreConditionS X k ↔
      ∀ x : X,
        WithBot.some (moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x) : ℕ∞) ≥
          min (k : WithBot ℕ∞) (ringKrullDim (X.presheaf.stalk x)))
