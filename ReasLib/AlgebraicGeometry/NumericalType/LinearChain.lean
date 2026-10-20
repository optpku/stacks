module

public import Mathlib.Data.Fin.Rev
public import ReasLib.AlgebraicGeometry.NumericalType
public import ReasLib.AlgebraicGeometry.NumericalType.MinusTwoIndex

@[expose] public section

namespace NumericalType

/-- The three possible weighted configurations of a linearly ordered chain in a
numerical type. -/
public def IsLinearChainConfiguration (T : NumericalType) {t : ℕ}
    (v : Fin t ↪ Fin T.n) : Prop :=
  (∃ w : ℕ,
    (∀ r, T.weight (v r) = w) ∧
    (∀ r s, r.val + 1 = s.val → T.intersection (v r) (v s) = w) ∧
    (∀ r s, r.val + 1 < s.val → T.intersection (v r) (v s) = 0)) ∨
  (∃ w : ℕ,
    (∀ r, r.val + 1 < t → T.weight (v r) = w) ∧
    (∀ r, r.val + 1 = t → T.weight (v r) = 2 * w) ∧
    (∀ r s, r.val + 1 = s.val → s.val + 1 < t →
      T.intersection (v r) (v s) = w) ∧
    (∀ r s, r.val + 1 = s.val → s.val + 1 = t →
      T.intersection (v r) (v s) = 2 * w) ∧
    (∀ r s, r.val + 1 < s.val → T.intersection (v r) (v s) = 0)) ∨
  (∃ w : ℕ,
    (∀ r, r.val + 1 < t → T.weight (v r) = 2 * w) ∧
    (∀ r, r.val + 1 = t → T.weight (v r) = w) ∧
    (∀ r s, r.val + 1 = s.val → T.intersection (v r) (v s) = 2 * w) ∧
    (∀ r s, r.val + 1 < s.val → T.intersection (v r) (v s) = 0))

/-- A chain of more than five consecutive `(-2)`-indices in a numerical type has
one of the three weighted linear-chain configurations, up to reversing its order. -/
theorem linearChainClassification (T : NumericalType) (t : ℕ) (ht : 5 < t)
    (hn : t < T.n) (v : Fin t ↪ Fin T.n)
    (hminusTwo : ∀ r,
      IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r))
    (hchain : ∀ r s, r.val + 1 = s.val →
      T.intersection (v r) (v s) ≠ 0) :
    IsLinearChainConfiguration T v ∨
      IsLinearChainConfiguration T ((Fin.revPerm : Equiv.Perm (Fin t)).toEmbedding.trans v) := sorry

end NumericalType
