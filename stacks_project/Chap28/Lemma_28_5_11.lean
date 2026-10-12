/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Noetherian.Specialization
import StacksCheckRecall

open TopologicalSpace

universe u

/- Lemma 28.5.11: every infinite subset of a Noetherian scheme contains an infinite subset with
no nontrivial specializations among its points. -/
@[stacks 0CXG] #check
  (AlgebraicGeometry.Scheme.exists_infinite_subset_without_nontrivial_specializations :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] {T : Set S},
      T.Infinite → ∃ T' ⊆ T, T'.Infinite ∧ IsAntichain (· ⤳ ·) T')
