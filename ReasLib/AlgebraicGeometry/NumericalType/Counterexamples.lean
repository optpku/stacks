/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.NumericalType.Minimality
public import ReasLib.AlgebraicGeometry.NumericalType.SpecialFiber

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped BigOperators

noncomputable section

universe u

namespace NumericalType.ModelCounterexample

/-- Positivity of the one-element index set used by the first counterexample. -/
private theorem singleNPos : 0 < 1 := sorry

/-- Positivity of the multiplicity in the first counterexample. -/
private theorem singleMultiplicityPos : ∀ _ : Fin 1, 0 < 1 := sorry

/-- Positivity of the weight in the first counterexample. -/
private theorem singleWeightPos : ∀ _ : Fin 1, 0 < 6 := sorry

/-- Symmetry of the zero intersection matrix in the first counterexample. -/
private theorem singleSymmetric : ∀ i j : Fin 1, (0 : ℤ) = 0 := sorry

/-- Off-diagonal nonnegativity of the first counterexample matrix. -/
private theorem singleOffDiagonalNonnegative :
    ∀ i j : Fin 1, i ≠ j → 0 ≤ (0 : ℤ) := sorry

/-- Connectedness of the one-index intersection data. -/
private theorem singleConnected :
    ∀ I : Set (Fin 1), I.Nonempty → I ≠ Set.univ →
      ∃ i ∈ I, ∃ j ∉ I, (0 : ℤ) ≠ 0 := sorry

/-- The multiplicity-weighted row sum for the first counterexample vanishes. -/
private theorem singleRowSumEqZero :
    ∀ i : Fin 1, ∑ _j : Fin 1, (0 : ℤ) * ((1 : ℕ) : ℤ) = 0 := sorry

/-- The weight of the first counterexample divides every matrix entry. -/
private theorem singleWeightDvd :
    ∀ i j : Fin 1, ((6 : ℕ) : ℤ) ∣ (0 : ℤ) := sorry

/-- The explicit one-component numerical type with weight six and genus one. -/
public def single : NumericalType where
  n := 1
  n_pos := singleNPos
  multiplicity := fun _ ↦ 1
  intersection := fun _ _ ↦ 0
  weight := fun _ ↦ 6
  componentGenus := fun _ ↦ 1
  multiplicity_pos := singleMultiplicityPos
  weight_pos := singleWeightPos
  symmetric := singleSymmetric
  offDiagonal_nonnegative := singleOffDiagonalNonnegative
  connected := singleConnected
  rowSum_eq_zero := singleRowSumEqZero
  weight_dvd := singleWeightDvd

/-- The one-component counterexample has exactly one index. -/
public theorem single_n : single.n = 1 := sorry

/-- The multiplicity of the unique component is one. -/
public theorem single_multiplicity (i : Fin single.n) : single.multiplicity i = 1 := sorry

/-- Every entry of the first intersection matrix is zero. -/
public theorem single_intersection (i j : Fin single.n) : single.intersection i j = 0 := sorry

/-- The component weight is six. -/
public theorem single_weight (i : Fin single.n) : single.weight i = 6 := sorry

/-- The component genus is one. -/
public theorem single_componentGenus (i : Fin single.n) : single.componentGenus i = 1 := sorry

/-- The first counterexample is minimal. -/
public theorem single_isMinimal : single.IsMinimal := sorry

/-- The first counterexample has genus one. -/
public theorem single_genus : single.genus = 1 := sorry

/-- Positivity of the two-element index set used by the second counterexample. -/
private theorem pairNPos : 0 < 2 := sorry

/-- Positivity of the multiplicities in the second counterexample. -/
private theorem pairMultiplicityPos : ∀ _ : Fin 2, 0 < 1 := sorry

/-- Positivity of the weights in the second counterexample. -/
private theorem pairWeightPos : ∀ _ : Fin 2, 0 < 6 := sorry

/-- Symmetry of the second counterexample matrix. -/
private theorem pairSymmetric : ∀ i j : Fin 2,
    (if i = j then -6 else 6 : ℤ) = if j = i then -6 else 6 := sorry

/-- Off-diagonal nonnegativity of the second counterexample matrix. -/
private theorem pairOffDiagonalNonnegative : ∀ i j : Fin 2, i ≠ j →
    0 ≤ (if i = j then -6 else 6 : ℤ) := sorry

/-- Connectedness of the two-index intersection data. -/
private theorem pairConnected :
    ∀ I : Set (Fin 2), I.Nonempty → I ≠ Set.univ →
      ∃ i ∈ I, ∃ j ∉ I, (if i = j then -6 else 6 : ℤ) ≠ 0 := sorry

/-- The multiplicity-weighted row sums for the second counterexample vanish. -/
private theorem pairRowSumEqZero : ∀ i : Fin 2,
    ∑ j : Fin 2, (if i = j then -6 else 6 : ℤ) * ((1 : ℕ) : ℤ) = 0 := sorry

/-- The weight in the second counterexample divides every matrix entry. -/
private theorem pairWeightDvd : ∀ i j : Fin 2,
    ((6 : ℕ) : ℤ) ∣ (if i = j then -6 else 6 : ℤ) := sorry

/-- The explicit two-component numerical type with weights six and component genera one. -/
public def pair : NumericalType where
  n := 2
  n_pos := pairNPos
  multiplicity := fun _ ↦ 1
  intersection := fun i j ↦ if i = j then -6 else 6
  weight := fun _ ↦ 6
  componentGenus := fun _ ↦ 1
  multiplicity_pos := pairMultiplicityPos
  weight_pos := pairWeightPos
  symmetric := pairSymmetric
  offDiagonal_nonnegative := pairOffDiagonalNonnegative
  connected := pairConnected
  rowSum_eq_zero := pairRowSumEqZero
  weight_dvd := pairWeightDvd

/-- The two-component counterexample has exactly two indices. -/
public theorem pair_n : pair.n = 2 := sorry

/-- Both component multiplicities are one. -/
public theorem pair_multiplicity (i : Fin pair.n) : pair.multiplicity i = 1 := sorry

/-- The second intersection matrix has diagonal `-6` and off-diagonal `6`. -/
public theorem pair_intersection (i j : Fin pair.n) :
    pair.intersection i j = if i = j then -6 else 6 := sorry

/-- Both component weights are six. -/
public theorem pair_weight (i : Fin pair.n) : pair.weight i = 6 := sorry

/-- Both component genera are one. -/
public theorem pair_componentGenus (i : Fin pair.n) : pair.componentGenus i = 1 := sorry

/-- The second counterexample is minimal. -/
public theorem pair_isMinimal : pair.IsMinimal := sorry

/-- The second counterexample has genus seven. -/
public theorem pair_genus : pair.genus = 7 := sorry

/-- The one-component numerical type cannot arise from a model with the stated generic fibre. -/
public theorem single_not_isSpecialFiberType
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f]
    [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (h_generic : Smooth (pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
      GeometricallyIntegral (pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
      topologicalKrullDim (pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) : Scheme) = 1) :
    ¬ NumericalType.IsSpecialFiberType single R K f h_generic := sorry

/-- The two-component numerical type cannot arise from a model with the stated generic fibre. -/
public theorem pair_not_isSpecialFiberType
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f]
    [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (h_generic : Smooth (pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
      GeometricallyIntegral (pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
      topologicalKrullDim (pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) : Scheme) = 1) :
    ¬ NumericalType.IsSpecialFiberType pair R K f h_generic := sorry

end NumericalType.ModelCounterexample

namespace NumericalType

/-- There exists a numerical type of negative genus. -/
public theorem exists_negativeGenus : ∃ T : NumericalType, T.genus < 0 := sorry

/-- A numerical type of negative genus cannot arise from a model with the stated generic fibre. -/
public theorem negativeGenus_not_isSpecialFiberType
    (T : NumericalType) (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f]
    [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (h_generic : Smooth (pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
      GeometricallyIntegral (pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
      topologicalKrullDim (pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) : Scheme) = 1)
    (hgenus : T.genus < 0) :
    ¬ T.IsSpecialFiberType R K f h_generic := sorry

end NumericalType
