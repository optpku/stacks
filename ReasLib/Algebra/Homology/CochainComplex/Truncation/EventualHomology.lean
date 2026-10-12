/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Truncation replacements from eventual homology vanishing

These statements expose the canonical lower, upper, and two-sided truncation maps as the reusable
replacement API.  The support bounds remain ordinary propositions in the conclusions; proof users
may feed them to Mathlib's `quasiIso_*_iff` theorems without rebuilding local instances.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Truncation

namespace GE

/-- Vanishing below `a` makes the canonical lower-truncation projection a quasi-isomorphism. -/
@[stacks 05RV "lower truncation replacement"]
theorem quasiIso_of_vanishes (K : CochainComplex C ℤ) (a : ℤ)
    (hK : ∀ n : ℤ, n < a → IsZero (K.homology n)) :
    QuasiIso (K.πTruncGE a) := sorry

/-- The canonical lower truncation is strictly supported in degrees at least `a`. -/
@[stacks 05RV "lower truncation replacement"]
theorem isStrictlyGE (K : CochainComplex C ℤ) (a : ℤ) :
    (K.truncGE a).IsStrictlyGE a := sorry

/-- Eventual vanishing below a bound gives a quasi-isomorphic lower truncation. -/
@[stacks 05RV "lower truncation replacement"]
theorem exists_of_eventually_isZero (K : CochainComplex C ℤ)
    (hK : ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (K.homology n)) :
    ∃ a : ℤ, QuasiIso (K.πTruncGE a) ∧ (K.truncGE a).IsStrictlyGE a := sorry

end GE

namespace LE

/-- Vanishing above `b` makes the canonical upper-truncation inclusion a quasi-isomorphism. -/
@[stacks 05RV "upper truncation replacement"]
theorem quasiIso_of_vanishes (K : CochainComplex C ℤ) (b : ℤ)
    (hK : ∀ n : ℤ, b < n → IsZero (K.homology n)) :
    QuasiIso (K.ιTruncLE b) := sorry

/-- The canonical upper truncation is strictly supported in degrees at most `b`. -/
@[stacks 05RV "upper truncation replacement"]
theorem isStrictlyLE (K : CochainComplex C ℤ) (b : ℤ) :
    (K.truncLE b).IsStrictlyLE b := sorry

/-- Eventual vanishing above a bound gives a quasi-isomorphic upper truncation. -/
@[stacks 05RV "upper truncation replacement"]
theorem exists_of_eventually_isZero (K : CochainComplex C ℤ)
    (hK : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (K.homology n)) :
    ∃ b : ℤ, QuasiIso (K.ιTruncLE b) ∧ (K.truncLE b).IsStrictlyLE b := sorry

end LE

namespace Bounded

/-- The canonical two-sided truncation square is a bounded replacement of `K` between `a`
and `b`.

All four maps are canonical truncation maps, so this predicate records only their mathematical
properties and introduces no chosen data. -/
@[stacks 05RV "two-sided truncation replacement square"]
structure IsReplacement (K : CochainComplex C ℤ) (a b : ℤ) : Prop where
  /-- The lower bound does not exceed the upper bound. -/
  bounds : a ≤ b
  /-- The projection to the lower truncation is a quasi-isomorphism. -/
  toGEQuasiIso : QuasiIso (K.πTruncGE a)
  /-- The inclusion from the upper truncation is a quasi-isomorphism. -/
  fromLEQuasiIso : QuasiIso (K.ιTruncLE b)
  /-- The projection from the upper truncation to the two-sided truncation is a
  quasi-isomorphism. -/
  leToBoundedQuasiIso : QuasiIso ((K.truncLE b).πTruncGE a)
  /-- The comparison from the two-sided truncation to the lower truncation is a
  quasi-isomorphism. -/
  boundedToGEQuasiIso : QuasiIso (truncGEMap (K.ιTruncLE b) a)
  /-- The canonical truncation square commutes. -/
  commSq : CommSq ((K.truncLE b).πTruncGE a) (K.ιTruncLE b)
    (truncGEMap (K.ιTruncLE b) a) (K.πTruncGE a)
  /-- The two-sided truncation is strictly supported in degrees at least `a`. -/
  boundedGE : ((K.truncLE b).truncGE a).IsStrictlyGE a
  /-- The two-sided truncation is strictly supported in degrees at most `b`. -/
  boundedLE : ((K.truncLE b).truncGE a).IsStrictlyLE b

/-- The componentwise specification of a canonical two-sided truncation replacement. -/
@[stacks 05RV "two-sided truncation replacement square"]
theorem isReplacement_iff (K : CochainComplex C ℤ) (a b : ℤ) :
    IsReplacement K a b ↔
      a ≤ b ∧
      QuasiIso (K.πTruncGE a) ∧
      QuasiIso (K.ιTruncLE b) ∧
      QuasiIso ((K.truncLE b).πTruncGE a) ∧
      QuasiIso (truncGEMap (K.ιTruncLE b) a) ∧
      CommSq ((K.truncLE b).πTruncGE a) (K.ιTruncLE b)
        (truncGEMap (K.ιTruncLE b) a) (K.πTruncGE a) ∧
      ((K.truncLE b).truncGE a).IsStrictlyGE a ∧
      ((K.truncLE b).truncGE a).IsStrictlyLE b := sorry

/-- Construct a bounded truncation replacement from its eight componentwise conditions. -/
@[stacks 05RV "two-sided truncation replacement square"]
def IsReplacement.ofConditions (K : CochainComplex C ℤ) (a b : ℤ)
    (h : a ≤ b ∧
      QuasiIso (K.πTruncGE a) ∧
      QuasiIso (K.ιTruncLE b) ∧
      QuasiIso ((K.truncLE b).πTruncGE a) ∧
      QuasiIso (truncGEMap (K.ιTruncLE b) a) ∧
      CommSq ((K.truncLE b).πTruncGE a) (K.ιTruncLE b)
        (truncGEMap (K.ιTruncLE b) a) (K.πTruncGE a) ∧
      ((K.truncLE b).truncGE a).IsStrictlyGE a ∧
      ((K.truncLE b).truncGE a).IsStrictlyLE b) :
    IsReplacement K a b :=
  { bounds := h.1
    toGEQuasiIso := h.2.1
    fromLEQuasiIso := h.2.2.1
    leToBoundedQuasiIso := h.2.2.2.1
    boundedToGEQuasiIso := h.2.2.2.2.1
    commSq := h.2.2.2.2.2.1
    boundedGE := h.2.2.2.2.2.2.1
    boundedLE := h.2.2.2.2.2.2.2 }

/-- Fixed lower and upper homology-vanishing bounds give the canonical bounded replacement
square. -/
@[stacks 05RV "two-sided truncation replacement square"]
theorem isReplacement_of_vanishes (K : CochainComplex C ℤ) (a b : ℤ) (hab : a ≤ b)
    (hBelow : ∀ n : ℤ, n < a → IsZero (K.homology n))
    (hAbove : ∀ n : ℤ, b < n → IsZero (K.homology n)) :
    IsReplacement K a b := sorry

/-- Finite-range homology gives bounds carrying a canonical bounded truncation replacement square. -/
@[stacks 05RV "two-sided truncation replacement square"]
theorem exists_of_eventually_isZero (K : CochainComplex C ℤ)
    (hK : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K.homology n)) :
    ∃ a b : ℤ, IsReplacement K a b := sorry

end Bounded

end Truncation



end CochainComplex
