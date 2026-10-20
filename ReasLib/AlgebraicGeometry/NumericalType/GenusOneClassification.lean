/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.LinearAlgebra.Matrix.Notation
public import ReasLib.AlgebraicGeometry.NumericalType.Equivalence
public import ReasLib.AlgebraicGeometry.NumericalType.Genus
public import ReasLib.AlgebraicGeometry.NumericalType.Minimality

@[expose] public section

namespace NumericalType

/-- A numerical type has the specified multiplicities, intersections, weights, and
component genera after reindexing, with multiplicities scaled by `m` and intersections
and weights scaled by `w`. -/
public structure HasScaledConfiguration (T : NumericalType) {n : ℕ}
    (e : Fin n ≃ Fin T.n) (m w : ℕ)
    (multiplicityCoefficients weightCoefficients componentGenera : Fin n → ℕ)
    (intersectionCoefficients : Matrix (Fin n) (Fin n) ℤ) : Prop where
  /-- The multiplicity data after relabeling. -/
  multiplicity_eq : T.multiplicity ∘ e =
    (fun i ↦ multiplicityCoefficients i * m)
  /-- The intersection data after relabeling and scaling. -/
  intersection_eq : T.intersection.submatrix e e =
    (fun i j ↦ intersectionCoefficients i j * (w : ℤ))
  /-- The weight data after relabeling. -/
  weight_eq : T.weight ∘ e =
    (fun i ↦ weightCoefficients i * w)
  /-- The component-genus data after relabeling. -/
  componentGenus_eq : T.componentGenus ∘ e = componentGenera

/-- Construct a scaled configuration from its four defining data equalities. -/
public def HasScaledConfiguration.of (T : NumericalType) {n : ℕ}
    (e : Fin n ≃ Fin T.n) (m w : ℕ)
    (multiplicityCoefficients weightCoefficients componentGenera : Fin n → ℕ)
    (intersectionCoefficients : Matrix (Fin n) (Fin n) ℤ)
    (multiplicity_eq : T.multiplicity ∘ e =
      (fun i ↦ multiplicityCoefficients i * m))
    (intersection_eq : T.intersection.submatrix e e =
      (fun i j ↦ intersectionCoefficients i j * (w : ℤ)))
    (weight_eq : T.weight ∘ e =
      (fun i ↦ weightCoefficients i * w))
    (componentGenus_eq : T.componentGenus ∘ e = componentGenera) :
    HasScaledConfiguration T e m w multiplicityCoefficients weightCoefficients
      componentGenera intersectionCoefficients :=
  { multiplicity_eq := multiplicity_eq
    intersection_eq := intersection_eq
    weight_eq := weight_eq
    componentGenus_eq := componentGenus_eq }

/-- Two increasing indices are consecutive in a linearly ordered configuration. -/
public abbrev IsLinearEdge {n : ℕ} (i j : Fin n) : Prop :=
  i.val + 1 = j.val

/-- Two increasing indices form an edge of the cyclic configuration on `n` vertices. -/
public abbrev IsCycleEdge (n : ℕ) (i j : Fin n) : Prop :=
  IsLinearEdge i j ∨ (i.val = 0 ∧ j.val + 1 = n)

/-- Two increasing indices form an edge of the forked chain whose last vertex
branches from the penultimate vertex of the underlying chain. -/
public abbrev IsForkedChainEdge (n : ℕ) (i j : Fin n) : Prop :=
  (IsLinearEdge i j ∧ j.val + 1 < n) ∨
    (i.val + 2 = j.val ∧ j.val + 1 = n)

/-- Two increasing indices form an edge of a chain with a pair of leaves at each end. -/
public abbrev IsDoubleForkedChainEdge (n : ℕ) (i j : Fin n) : Prop :=
  (i.val = 0 ∧ j.val = 2) ∨
    (1 ≤ i.val ∧ IsLinearEdge i j ∧ j.val + 1 < n) ∨
    (i.val + 2 = j.val ∧ j.val + 1 = n)

/-- A numerical type belongs, up to reindexing, to one of the thirty-four genus-one
configurations. Fixed configurations specify all four numerical arrays; the seven
variable families specify their multiplicities, off-diagonal intersections, weights,
and zero component genera. -/
public inductive IsGenusOneConfiguration (T : NumericalType) : Prop where
  /-- The one-component configuration of component genus one. -/
  | oneEllipticComponent (m w : ℕ) (hm : 0 < m) (hw : 0 < w)
      (e : Fin 1 ≃ Fin T.n)
      (hmatches : HasScaledConfiguration T e m w ![1] ![1] ![1] ![![0]])
  /-- The uniform two-component configuration with double intersection. -/
  | twoUniform (m w : ℕ) (hm : 0 < m) (hw : 0 < w)
      (e : Fin 2 ≃ Fin T.n)
      (hmatches : HasScaledConfiguration T e m w ![1, 1] ![1, 1] ![0, 0]
        ![![-2, 2], ![2, -2]])
  /-- The two-component configuration with multiplicity ratio `2 : 1`. -/
  | twoQuadrupleEdge (m w : ℕ) (hm : 0 < m) (hw : 0 < w)
      (e : Fin 2 ≃ Fin T.n)
      (hmatches : HasScaledConfiguration T e m w ![2, 1] ![1, 4] ![0, 0]
        ![![-2, 4], ![4, -8]])
  /-- The uniform triangular three-component configuration. -/
  | threeCycle (m w : ℕ) (hm : 0 < m) (hw : 0 < w)
      (e : Fin 3 ≃ Fin T.n)
      (hmatches : HasScaledConfiguration T e m w ![1, 1, 1] ![1, 1, 1] ![0, 0, 0]
        ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]])
  /-- The three-component chain with a triple-weight endpoint. -/
  | threeTripleEndpoint (m w : ℕ) (hm : 0 < m) (hw : 0 < w)
      (e : Fin 3 ≃ Fin T.n)
      (hmatches : HasScaledConfiguration T e m w ![1, 2, 1] ![1, 1, 3] ![0, 0, 0]
        ![![-2, 1, 0], ![1, -2, 3], ![0, 3, -6]])
  /-- The three-component chain with increasing multiplicities. -/
  | threeIncreasing (m w : ℕ) (hm : 0 < m) (hw : 0 < w)
      (e : Fin 3 ≃ Fin T.n)
      (hmatches : HasScaledConfiguration T e m w ![1, 2, 3] ![3, 3, 1] ![0, 0, 0]
        ![![-6, 3, 0], ![3, -6, 3], ![0, 3, -2]])
  /-- The three-component chain with successively doubled weights. -/
  | threeDoubling (m w : ℕ) (hm : 0 < m) (hw : 0 < w)
      (e : Fin 3 ≃ Fin T.n)
      (hmatches : HasScaledConfiguration T e m w ![2, 2, 1] ![1, 2, 4] ![0, 0, 0]
        ![![-2, 2, 0], ![2, -4, 4], ![0, 4, -8]])
  /-- The three-component chain with a heavier middle component and uniform multiplicity. -/
  | threeHeavyMiddle (m w : ℕ) (hm : 0 < m) (hw : 0 < w)
      (e : Fin 3 ≃ Fin T.n)
      (hmatches : HasScaledConfiguration T e m w ![1, 1, 1] ![1, 2, 1] ![0, 0, 0]
        ![![-2, 2, 0], ![2, -4, 2], ![0, 2, -2]])
  /-- The three-component chain with a lighter middle component. -/
  | threeLightMiddle (m w : ℕ) (hm : 0 < m) (hw : 0 < w)
      (e : Fin 3 ≃ Fin T.n)
      (hmatches : HasScaledConfiguration T e m w ![1, 2, 1] ![2, 1, 2] ![0, 0, 0]
        ![![-4, 2, 0], ![2, -2, 2], ![0, 2, -4]])
  /-- The uniform four-cycle configuration. -/
  | fourCycle (m w : ℕ) (hm : 0 < m) (hw : 0 < w)
      (e : Fin 4 ≃ Fin T.n)
      (hmatches : HasScaledConfiguration T e m w ![1, 1, 1, 1] ![1, 1, 1, 1]
        ![0, 0, 0, 0]
        ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![0, 1, -2, 1], ![1, 0, 1, -2]])
  /-- The four-component chain with a quadruple-weight endpoint. -/
  | fourQuadrupleEndpoint (m w : ℕ) (hm : 0 < m) (hw : 0 < w)
      (e : Fin 4 ≃ Fin T.n)
      (hmatches : HasScaledConfiguration T e m w ![2, 2, 2, 1] ![1, 2, 2, 4]
        ![0, 0, 0, 0]
        ![![-2, 2, 0, 0], ![2, -4, 2, 0], ![0, 2, -4, 4], ![0, 0, 4, -8]])
  /-- The four-component chain with uniform multiplicity and lighter endpoints. -/
  | fourUniformMultiplicity (m w : ℕ) (hm : 0 < m) (hw : 0 < w)
      (e : Fin 4 ≃ Fin T.n)
      (hmatches : HasScaledConfiguration T e m w ![1, 1, 1, 1] ![1, 2, 2, 1]
        ![0, 0, 0, 0]
        ![![-2, 2, 0, 0], ![2, -4, 2, 0], ![0, 2, -4, 2], ![0, 0, 2, -2]])
  /-- The symmetric four-component weighted chain. -/
  | fourSymmetricChain (m w : ℕ) (hm : 0 < m) (hw : 0 < w)
      (e : Fin 4 ≃ Fin T.n)
      (hmatches : HasScaledConfiguration T e m w ![1, 2, 2, 1] ![2, 1, 1, 2]
        ![0, 0, 0, 0]
        ![![-4, 2, 0, 0], ![2, -2, 1, 0], ![0, 1, -2, 2], ![0, 0, 2, -4]])
  /-- The four-component fork with one double-weight leaf. -/
  | fourFork (m w : ℕ) (hm : 0 < m) (hw : 0 < w)
      (e : Fin 4 ≃ Fin T.n)
      (hmatches : HasScaledConfiguration T e m w ![2, 1, 1, 1] ![1, 1, 1, 2]
        ![0, 0, 0, 0]
        ![![-2, 1, 1, 2], ![1, -2, 0, 0], ![1, 0, -2, 0], ![2, 0, 0, -4]])
  /-- The four-component fork with a light final leaf. -/
  | fourWeightedFork (m w : ℕ) (hm : 0 < m) (hw : 0 < w)
      (e : Fin 4 ≃ Fin T.n)
      (hmatches : HasScaledConfiguration T e m w ![2, 1, 1, 2] ![2, 2, 2, 1]
        ![0, 0, 0, 0]
        ![![-4, 2, 2, 2], ![2, -4, 0, 0], ![2, 0, -4, 0], ![2, 0, 0, -2]])
  /-- The uniform five-cycle configuration. -/
  | fiveCycle (m w : ℕ) (hm : 0 < m) (hw : 0 < w)
      (e : Fin 5 ≃ Fin T.n)
      (hmatches : HasScaledConfiguration T e m w ![1, 1, 1, 1, 1] ![1, 1, 1, 1, 1]
        ![0, 0, 0, 0, 0]
        ![![-2, 1, 0, 0, 1], ![1, -2, 1, 0, 0], ![0, 1, -2, 1, 0],
          ![0, 0, 1, -2, 1], ![1, 0, 0, 1, -2]])
  /-- The first asymmetric five-component chain. -/
  | fiveAscendingThenDescending (m w : ℕ) (hm : 0 < m) (hw : 0 < w)
      (e : Fin 5 ≃ Fin T.n)
      (hmatches : HasScaledConfiguration T e m w ![1, 2, 3, 2, 1] ![1, 1, 1, 2, 2]
        ![0, 0, 0, 0, 0]
        ![![-2, 1, 0, 0, 0], ![1, -2, 1, 0, 0], ![0, 1, -2, 2, 0],
          ![0, 0, 2, -4, 2], ![0, 0, 0, 2, -4]])
  /-- The second asymmetric five-component chain. -/
  | fiveIncreasing (m w : ℕ) (hm : 0 < m) (hw : 0 < w)
      (e : Fin 5 ≃ Fin T.n)
      (hmatches : HasScaledConfiguration T e m w ![1, 2, 3, 4, 2] ![2, 2, 2, 1, 1]
        ![0, 0, 0, 0, 0]
        ![![-4, 2, 0, 0, 0], ![2, -4, 2, 0, 0], ![0, 2, -4, 2, 0],
          ![0, 0, 2, -2, 1], ![0, 0, 0, 1, -2]])
  /-- The five-component chain with a quadruple-weight endpoint. -/
  | fiveQuadrupleEndpoint (m w : ℕ) (hm : 0 < m) (hw : 0 < w)
      (e : Fin 5 ≃ Fin T.n)
      (hmatches : HasScaledConfiguration T e m w ![2, 2, 2, 2, 1] ![1, 2, 2, 2, 4]
        ![0, 0, 0, 0, 0]
        ![![-2, 2, 0, 0, 0], ![2, -4, 2, 0, 0], ![0, 2, -4, 2, 0],
          ![0, 0, 2, -4, 4], ![0, 0, 0, 4, -8]])
  /-- The uniform-multiplicity five-component chain. -/
  | fiveUniformMultiplicity (m w : ℕ) (hm : 0 < m) (hw : 0 < w)
      (e : Fin 5 ≃ Fin T.n)
      (hmatches : HasScaledConfiguration T e m w ![1, 1, 1, 1, 1] ![1, 2, 2, 2, 1]
        ![0, 0, 0, 0, 0]
        ![![-2, 2, 0, 0, 0], ![2, -4, 2, 0, 0], ![0, 2, -4, 2, 0],
          ![0, 0, 2, -4, 2], ![0, 0, 0, 2, -2]])
  /-- The symmetric five-component weighted chain. -/
  | fiveSymmetricChain (m w : ℕ) (hm : 0 < m) (hw : 0 < w)
      (e : Fin 5 ≃ Fin T.n)
      (hmatches : HasScaledConfiguration T e m w ![1, 2, 2, 2, 1] ![2, 1, 1, 1, 2]
        ![0, 0, 0, 0, 0]
        ![![-4, 2, 0, 0, 0], ![2, -2, 1, 0, 0], ![0, 1, -2, 1, 0],
          ![0, 0, 1, -2, 2], ![0, 0, 0, 2, -4]])
  /-- The five-component four-leaf fork. -/
  | fiveFourLeafFork (m w : ℕ) (hm : 0 < m) (hw : 0 < w)
      (e : Fin 5 ≃ Fin T.n)
      (hmatches : HasScaledConfiguration T e m w ![2, 1, 1, 1, 1] ![1, 1, 1, 1, 1]
        ![0, 0, 0, 0, 0]
        ![![-2, 1, 1, 1, 1], ![1, -2, 0, 0, 0], ![1, 0, -2, 0, 0],
          ![1, 0, 0, -2, 0], ![1, 0, 0, 0, -2]])
  /-- The five-component fork with two short leaves. -/
  | fiveFork (m w : ℕ) (hm : 0 < m) (hw : 0 < w)
      (e : Fin 5 ≃ Fin T.n)
      (hmatches : HasScaledConfiguration T e m w ![1, 2, 2, 1, 1] ![2, 1, 1, 1, 1]
        ![0, 0, 0, 0, 0]
        ![![-4, 2, 0, 0, 0], ![2, -2, 1, 0, 0], ![0, 1, -2, 1, 1],
          ![0, 0, 1, -2, 0], ![0, 0, 1, 0, -2]])
  /-- The five-component doubled fork. -/
  | fiveDoubledFork (m w : ℕ) (hm : 0 < m) (hw : 0 < w)
      (e : Fin 5 ≃ Fin T.n)
      (hmatches : HasScaledConfiguration T e m w ![2, 2, 2, 1, 1] ![1, 2, 2, 2, 2]
        ![0, 0, 0, 0, 0]
        ![![-2, 2, 0, 0, 0], ![2, -4, 2, 0, 0], ![0, 2, -4, 2, 2],
          ![0, 0, 2, -4, 0], ![0, 0, 2, 0, -4]])
  /-- The variable uniform cycle family. -/
  | cycleFamily (n m w : ℕ) (hn : 6 ≤ n) (hm : 0 < m) (hw : 0 < w)
      (e : Fin n ≃ Fin T.n)
      (multiplicity_eq : ∀ i, T.multiplicity (e i) = m)
      (intersection_eq : ∀ i j, i < j → T.intersection (e i) (e j) =
        if IsCycleEdge n i j then (w : ℤ) else 0)
      (weight_eq : ∀ i, T.weight (e i) = w)
      (componentGenus_eq : ∀ i, T.componentGenus (e i) = 0)
  /-- The variable chain family with a quadruple-weight endpoint. -/
  | heavyEndpointChainFamily (n m w : ℕ) (hn : 6 ≤ n) (hm : 0 < m) (hw : 0 < w)
      (e : Fin n ≃ Fin T.n)
      (multiplicity_eq : ∀ i, T.multiplicity (e i) =
        if i.val + 1 = n then m else 2 * m)
      (intersection_eq : ∀ i j, i < j → T.intersection (e i) (e j) =
        if IsLinearEdge i j then
          if j.val + 1 = n then (4 * w : ℕ) else 2 * w else 0)
      (weight_eq : ∀ i, T.weight (e i) =
        if i.val = 0 then w else if i.val + 1 = n then 4 * w else 2 * w)
      (componentGenus_eq : ∀ i, T.componentGenus (e i) = 0)
  /-- The variable chain family with uniform multiplicity and light endpoints.
  The edge intersection is `2 * w`, as in the five-component configuration:
  the printed coefficient `w` in `item-up-chain-equal-down` contradicts divisibility
  by the interior weight `2 * w`. -/
  | uniformMultiplicityChainFamily (n m w : ℕ)
      (hn : 6 ≤ n) (hm : 0 < m) (hw : 0 < w) (e : Fin n ≃ Fin T.n)
      (multiplicity_eq : ∀ i, T.multiplicity (e i) = m)
      (intersection_eq : ∀ i j, i < j → T.intersection (e i) (e j) =
        if IsLinearEdge i j then (2 * w : ℕ) else 0)
      (weight_eq : ∀ i, T.weight (e i) =
        if i.val = 0 ∨ i.val + 1 = n then w else 2 * w)
      (componentGenus_eq : ∀ i, T.componentGenus (e i) = 0)
  /-- The variable symmetric chain family, with the row-sum-consistent multiplicities. -/
  | symmetricChainFamily (n m w : ℕ) (hn : 6 ≤ n) (hm : 0 < m) (hw : 0 < w)
      (e : Fin n ≃ Fin T.n)
      (firstMultiplicity_eq : ∀ i, i.val = 0 → T.multiplicity (e i) = m)
      (middleMultiplicity_eq : ∀ i, 0 < i.val → i.val + 1 < n →
        T.multiplicity (e i) = 2 * m)
      (lastMultiplicity_eq : ∀ i, i.val + 1 = n → T.multiplicity (e i) = m)
      (intersection_eq : ∀ i j, i < j → T.intersection (e i) (e j) =
        if IsLinearEdge i j then
          if i.val = 0 ∨ j.val + 1 = n then (2 * w : ℕ) else w else 0)
      (weight_eq : ∀ i, T.weight (e i) =
        if i.val = 0 ∨ i.val + 1 = n then 2 * w else w)
      (componentGenus_eq : ∀ i, T.componentGenus (e i) = 0)
  /-- The first variable forked-chain family. -/
  | forkedChainFamily (n m w : ℕ) (hn : 6 ≤ n) (hm : 0 < m) (hw : 0 < w)
      (e : Fin n ≃ Fin T.n)
      (firstMultiplicity_eq : ∀ i, i.val = 0 → T.multiplicity (e i) = m)
      (middleMultiplicity_eq : ∀ i, 1 ≤ i.val → i.val + 2 < n →
        T.multiplicity (e i) = 2 * m)
      (lastMultiplicities_eq : ∀ i, n ≤ i.val + 2 → T.multiplicity (e i) = m)
      (intersection_eq : ∀ i j, i < j → T.intersection (e i) (e j) =
        if IsForkedChainEdge n i j then
          if i.val = 0 then (2 * w : ℕ) else w else 0)
      (weight_eq : ∀ i, T.weight (e i) = if i.val = 0 then 2 * w else w)
      (componentGenus_eq : ∀ i, T.componentGenus (e i) = 0)
  /-- The second variable forked-chain family. -/
  | doubledForkedChainFamily (n m w : ℕ)
      (hn : 6 ≤ n) (hm : 0 < m) (hw : 0 < w) (e : Fin n ≃ Fin T.n)
      (initialMultiplicities_eq : ∀ i, i.val + 2 < n → T.multiplicity (e i) = 2 * m)
      (lastMultiplicities_eq : ∀ i, n ≤ i.val + 2 → T.multiplicity (e i) = m)
      (intersection_eq : ∀ i j, i < j → T.intersection (e i) (e j) =
        if IsForkedChainEdge n i j then (2 * w : ℕ) else 0)
      (weight_eq : ∀ i, T.weight (e i) = if i.val = 0 then w else 2 * w)
      (componentGenus_eq : ∀ i, T.componentGenus (e i) = 0)
  /-- The variable chain with an additional leaf at each end. -/
  | doubleForkedChainFamily (n m w : ℕ)
      (hn : 6 ≤ n) (hm : 0 < m) (hw : 0 < w) (e : Fin n ≃ Fin T.n)
      (endpointMultiplicities_eq : ∀ i, i.val < 2 ∨ n ≤ i.val + 2 →
        T.multiplicity (e i) = m)
      (middleMultiplicities_eq : ∀ i, 2 ≤ i.val → i.val + 2 < n →
        T.multiplicity (e i) = 2 * m)
      (intersection_eq : ∀ i j, i < j → T.intersection (e i) (e j) =
        if IsDoubleForkedChainEdge n i j then (w : ℤ) else 0)
      (weight_eq : ∀ i, T.weight (e i) = w)
      (componentGenus_eq : ∀ i, T.componentGenus (e i) = 0)
  /-- The exceptional seven-component configuration. -/
  | exceptionalSeven (m w : ℕ) (hm : 0 < m) (hw : 0 < w)
      (e : Fin 7 ≃ Fin T.n)
      (hmatches : HasScaledConfiguration T e m w ![1, 2, 3, 1, 2, 1, 2]
        ![1, 1, 1, 1, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0]
        ![![-2, 1, 0, 0, 0, 0, 0], ![1, -2, 1, 0, 0, 0, 0],
          ![0, 1, -2, 0, 1, 0, 1], ![0, 0, 0, -2, 1, 0, 0],
          ![0, 0, 1, 1, -2, 0, 0], ![0, 0, 0, 0, 0, -2, 1],
          ![0, 0, 1, 0, 0, 1, -2]])
  /-- The exceptional eight-component configuration. -/
  | exceptionalEight (m w : ℕ) (hm : 0 < m) (hw : 0 < w)
      (e : Fin 8 ≃ Fin T.n)
      (hmatches : HasScaledConfiguration T e m w ![1, 2, 3, 4, 3, 2, 1, 2]
        ![1, 1, 1, 1, 1, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0, 0]
        ![![-2, 1, 0, 0, 0, 0, 0, 0], ![1, -2, 1, 0, 0, 0, 0, 0],
          ![0, 1, -2, 1, 0, 0, 0, 0], ![0, 0, 1, -2, 1, 0, 0, 1],
          ![0, 0, 0, 1, -2, 1, 0, 0], ![0, 0, 0, 0, 1, -2, 1, 0],
          ![0, 0, 0, 0, 0, 1, -2, 0], ![0, 0, 0, 1, 0, 0, 0, -2]])
  /-- The exceptional nine-component configuration. -/
  | exceptionalNine (m w : ℕ) (hm : 0 < m) (hw : 0 < w)
      (e : Fin 9 ≃ Fin T.n)
      (hmatches : HasScaledConfiguration T e m w ![1, 2, 3, 4, 5, 6, 4, 2, 3]
        ![1, 1, 1, 1, 1, 1, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0, 0, 0]
        ![![-2, 1, 0, 0, 0, 0, 0, 0, 0], ![1, -2, 1, 0, 0, 0, 0, 0, 0],
          ![0, 1, -2, 1, 0, 0, 0, 0, 0], ![0, 0, 1, -2, 1, 0, 0, 0, 0],
          ![0, 0, 0, 1, -2, 1, 0, 0, 0], ![0, 0, 0, 0, 1, -2, 1, 0, 1],
          ![0, 0, 0, 0, 0, 1, -2, 1, 0], ![0, 0, 0, 0, 0, 0, 1, -2, 0],
          ![0, 0, 0, 0, 0, 1, 0, 0, -2]])

/-- The genus-one configuration predicate is invariant under a data-preserving relabeling. -/
public theorem isGenusOneConfiguration_iff_of_isRelabeling
    {T T' : NumericalType} {e : Fin T.n ≃ Fin T'.n} (h : IsRelabeling T T' e) :
    T.IsGenusOneConfiguration ↔ T'.IsGenusOneConfiguration := sorry

/-- The genus-one configuration predicate is invariant under a data-preserving equivalence. -/
public theorem isGenusOneConfiguration_iff_of_equivalent
    {T T' : NumericalType} (h : Equivalent T T') :
    T.IsGenusOneConfiguration ↔ T'.IsGenusOneConfiguration := sorry

/-- A numerical type is minimal of genus one if and only if it belongs, up to
data-preserving relabeling, to one of the thirty-four genus-one configurations. -/
public theorem genusOneClassification (T : NumericalType) :
    T.IsMinimal ∧ T.genus = 1 ↔ T.IsGenusOneConfiguration := sorry

end NumericalType
