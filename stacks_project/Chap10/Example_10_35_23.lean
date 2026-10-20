/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap10.Example_10_35_23.Index
public import Mathlib.Tactic.CrossRefAttribute
import stacks_project.Chap05.Lemma_5_8_4

/-!
# Irreducible components of a node and a matrix-product variety

@stack 00GF

The coordinate rings and the three closed subsets used below are explicit in
`Example_10_35_23.Index`.  This file records the two irreducible-component
computations from the source.
-/

@[expose] public section

universe u

noncomputable section

section Node

variable (k : Type u) [CommRing k] [IsDomain k]

/-- Example 10.35.23 (1): `Spec(k[x, y]/(xy))` has two irreducible components,
the `x`-axis and the `y`-axis. -/
@[stacks 00GF "(1)"]
theorem nodeCoordinateRing_irreducibleComponents :
    irreducibleComponents (PrimeSpectrum (nodeCoordinateRing k)) =
      {nodeXAxis k, nodeYAxis k} := by
  classical
  refine irreducibleComponents_eq_of_finite_irreducible_closed_cover
    {nodeXAxis k, nodeYAxis k} ?_ ?_ ?_ ?_ ?_
  · simp
  · ext p
    constructor
    · intro _
      simp
    · intro _
      have hxy : nodeCoordinate k 0 * nodeCoordinate k 1 ∈ p.asIdeal := by
        rw [node_coordinate_mul_eq_zero (k := k)]
        exact p.asIdeal.zero_mem
      have hor : p ∈ nodeXAxis k ∨ p ∈ nodeYAxis k := by
        rcases p.isPrime.mem_or_mem hxy with hx | hy
        · right
          simpa [nodeYAxis, PrimeSpectrum.mem_zeroLocus] using hx
        · left
          simpa [nodeXAxis, PrimeSpectrum.mem_zeroLocus] using hy
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hor
  · intro Z hZ
    have hZmem : Z = nodeXAxis k ∨ Z = nodeYAxis k := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hZ
    rcases hZmem with rfl | rfl
    · simpa [nodeXAxis] using PrimeSpectrum.isClosed_zeroLocus
        ({nodeCoordinate k 1} : Set (nodeCoordinateRing k))
    · simpa [nodeYAxis] using PrimeSpectrum.isClosed_zeroLocus
        ({nodeCoordinate k 0} : Set (nodeCoordinateRing k))
  · intro Z hZ
    have hZmem : Z = nodeXAxis k ∨ Z = nodeYAxis k := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hZ
    rcases hZmem with rfl | rfl
    · exact nodeXAxis_isIrreducible (k := k)
    · exact nodeYAxis_isIrreducible (k := k)
  · intro Z hZ
    have hZmem : Z = nodeXAxis k ∨ Z = nodeYAxis k := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hZ
    rcases hZmem with rfl | rfl
    · rintro hsubset
      obtain ⟨p, hpX, hpY⟩ := node_xAxis_has_off_yAxis_point (k := k)
      have hpUnion : p ∈ ⋃₀ ({nodeXAxis k, nodeYAxis k} \ {nodeXAxis k}) := hsubset hpX
      rcases Set.mem_sUnion.mp hpUnion with ⟨t, ht, hpt⟩
      have htMem : t = nodeXAxis k ∨ t = nodeYAxis k := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ht.1
      have htNe : t ≠ nodeXAxis k := by
        simpa [Set.mem_singleton_iff] using ht.2
      rcases htMem with rfl | rfl
      · exact False.elim (htNe rfl)
      · exact hpY hpt
    · rintro hsubset
      obtain ⟨p, hpY, hpX⟩ := node_yAxis_has_off_xAxis_point (k := k)
      have hpUnion : p ∈ ⋃₀ ({nodeXAxis k, nodeYAxis k} \ {nodeYAxis k}) := hsubset hpY
      rcases Set.mem_sUnion.mp hpUnion with ⟨t, ht, hpt⟩
      have htMem : t = nodeXAxis k ∨ t = nodeYAxis k := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ht.1
      have htNe : t ≠ nodeYAxis k := by
        simpa [Set.mem_singleton_iff] using ht.2
      rcases htMem with rfl | rfl
      · exact hpX hpt
      · exact False.elim (htNe rfl)

end Node

section MatrixProduct

variable (k : Type u) [Field k]

/-- Example 10.35.23 (2): the affine scheme of pairs of `2 × 2` matrices
`X` and `Y` satisfying `X * Y = 0` has three irreducible components: `Y = 0`,
`det X = det Y = 0`, and `X = 0`. -/
@[stacks 00GF "(2)"]
theorem matrixProductCoordinateRing_irreducibleComponents :
    irreducibleComponents (PrimeSpectrum (matrixProductCoordinateRing k)) =
      {matrixProductYZeroComponent k, matrixProductDeterminantZeroComponent k,
        matrixProductXZeroComponent k} := sorry

end MatrixProduct

#check @nodeCoordinateRing_irreducibleComponents
#check @matrixProductCoordinateRing_irreducibleComponents
