module

public import ReasLib.AlgebraicGeometry.NumericalType.LinearTwo
public import ReasLib.AlgebraicGeometry.NumericalType.LinearThree
public import ReasLib.AlgebraicGeometry.NumericalType.LinearFour
public import ReasLib.AlgebraicGeometry.NumericalType.LinearFive
public import ReasLib.AlgebraicGeometry.NumericalType.LinearChain
public import ReasLib.AlgebraicGeometry.NumericalType.ForkedChain
public import ReasLib.AlgebraicGeometry.NumericalType.ForkedFour
public import ReasLib.AlgebraicGeometry.NumericalType.ForkedFive
public import ReasLib.AlgebraicGeometry.NumericalType.ForkedSix
public import ReasLib.AlgebraicGeometry.NumericalType.ForkedSeven
public import ReasLib.AlgebraicGeometry.NumericalType.ForkedEight

@[expose] public section

namespace NumericalType

/-- The generic forked-chain configuration on an embedding of `t + 1` vertices. -/
public structure IsForkedChainConfiguration (T : NumericalType) {t : ℕ}
    (v : Fin (t + 1) ↪ Fin T.n) : Prop where
  /-- Every selected vertex has the same weight as the first one. -/
  weight_eq : ∀ r, T.weight (v r) = T.weight (v 0)
  /-- Every forked-chain edge has intersection equal to the common weight. -/
  edge_intersection : ∀ r s, IsForkEdge t r s →
    T.intersection (v r) (v s) = T.weight (v 0)
  /-- Every other lower-triangular intersection is zero. -/
  other_intersection : ∀ r s, s < r → ¬ IsForkEdge t s r →
    T.intersection (v r) (v s) = 0

namespace IsForkedChainConfiguration

set_option linter.defProp false in
/-- Construct a forked-chain configuration from its three defining conditions. -/
public def ofConditions {T : NumericalType} {t : ℕ}
    {v : Fin (t + 1) ↪ Fin T.n}
    (weight_eq : ∀ r, T.weight (v r) = T.weight (v 0))
    (edge_intersection : ∀ r s, IsForkEdge t r s →
      T.intersection (v r) (v s) = T.weight (v 0))
    (other_intersection : ∀ r s, s < r → ¬ IsForkEdge t s r →
      T.intersection (v r) (v s) = 0) :
    IsForkedChainConfiguration T v := sorry

end IsForkedChainConfiguration

/-- A proper finite subset of at least two `(-2)`-indices with no
zero-intersection cut is one of the listed linear or forked configurations. -/
public theorem minusTwoSubsetClassification (T : NumericalType)
    (I : Finset (Fin T.n))
    (hcard : 2 ≤ I.card)
    (hproper : I ≠ Finset.univ)
    (hminusTwo : ∀ i ∈ I,
      IsMinusTwoIndex T.componentGenus T.weight T.intersection i)
    (hconnected : ¬ ∃ J : Finset (Fin T.n),
      J.Nonempty ∧ J ⊆ I ∧ J ≠ I ∧
        ∀ i' ∈ J, ∀ i ∈ I \ J, T.intersection i' i = 0) :
    (∃ v₂ : Fin 2 ↪ Fin T.n,
      Finset.univ.map v₂ = I ∧ IsLinearTwoConfiguration T v₂) ∨
    (∃ v₃ : Fin 3 ↪ Fin T.n,
      Finset.univ.map v₃ = I ∧ IsLinearThreeConfiguration T v₃) ∨
    (∃ v₄ : Fin 4 ↪ Fin T.n,
      Finset.univ.map v₄ = I ∧
        (IsLinearFourConfiguration T v₄ ∨ IsForkedFourConfiguration T v₄)) ∨
    (∃ v₅ : Fin 5 ↪ Fin T.n,
      Finset.univ.map v₅ = I ∧
        (IsLinearFiveConfiguration T v₅ ∨ IsForkedFiveConfiguration T v₅)) ∨
    (∃ t : ℕ, 5 < t ∧ ∃ v : Fin t ↪ Fin T.n,
      Finset.univ.map v = I ∧ IsLinearChainConfiguration T v) ∨
    (∃ t : ℕ, 4 < t ∧ ∃ v : Fin (t + 1) ↪ Fin T.n,
      Finset.univ.map v = I ∧ IsForkedChainConfiguration T v) ∨
    (∃ v₆ : Fin 6 ↪ Fin T.n,
      Finset.univ.map v₆ = I ∧ IsForkedSixConfiguration T v₆) ∨
    (∃ v₇ : Fin 7 ↪ Fin T.n,
      Finset.univ.map v₇ = I ∧ IsForkedSevenConfiguration T v₇) ∨
    (∃ v₈ : Fin 8 ↪ Fin T.n,
      Finset.univ.map v₈ = I ∧ IsForkedEightConfiguration T v₈) := sorry

end NumericalType
