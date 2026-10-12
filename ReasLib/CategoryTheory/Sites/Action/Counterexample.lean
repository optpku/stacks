/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Data.ZMod.Basic
public import ReasLib.CategoryTheory.Action.Coinduction
public import ReasLib.CategoryTheory.Sites.Action.Restriction

/-!
# Counterexamples for action sites

This leaf packages the smallest action-site counterexample to finite-colimit
preservation of continuous direct image along restriction.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Action.Counterexample.TwoPoint

/-- The inclusion of the trivial group into the cyclic group of order two. -/
abbrev inclusion : PUnit →* Multiplicative (ZMod 2) := 1

/-- The two-element set with the trivial action of the trivial group. -/
abbrev trivialBool : Action (Type 0) PUnit := Action.trivial PUnit Bool

/-- Evaluation at the identity on maps coinduced from the trivial two-element action. -/
def evalOne : CoinducedMap inclusion trivialBool → Bool :=
  coinducedEvalOne inclusion trivialBool

/-- The continuous direct image along restriction from the two-element group to the trivial
group. -/
noncomputable def pushforward :=
  (Action.res (Type 0) inclusion).sheafPushforwardContinuous
    (Type 0) (Action.jointlySurjectiveTopology (Multiplicative (ZMod 2)))
    (Action.jointlySurjectiveTopology PUnit)

/-- Example 7.41.5 (08LS) (5): evaluation at the identity on this coinduced-map object is not
injective. -/
@[stacks 08LS "(5)"]
theorem evalOne_not_injective :
    ¬ Function.Injective evalOne := sorry

/-- Example 7.41.5 (08LS) (6): this continuous direct image does not preserve coequalizers. -/
@[stacks 08LS "(6)"]
theorem pushforward_not_preservesCoequalizers :
    ¬ PreservesColimitsOfShape WalkingParallelPair pushforward := sorry

/-- Example 7.41.5 (08LS) (7): this continuous direct image does not preserve pushouts. -/
@[stacks 08LS "(7)"]
theorem pushforward_not_preservesPushouts :
    ¬ PreservesColimitsOfShape WalkingSpan pushforward := sorry

end CategoryTheory.Action.Counterexample.TwoPoint
