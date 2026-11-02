/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Distance
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Open
public import ReasLib.RingTheory.Catenary.Basic
public import ReasLib.Topology.Specialization.Dimension
public import Mathlib.Topology.KrullDimension

@[expose] public section

open Set TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

private theorem codimBetween_self_zero {Y : Scheme.{u}} (y : Y) :
    TopologicalSpace.codimBetween (_root_.toIrreducibleCloseds y)
      (_root_.toIrreducibleCloseds y) le_rfl = 0 := by
  unfold TopologicalSpace.codimBetween
  rw [Order.coheight_eq_zero]
  intro x hx
  exact x.property.2

private theorem distanceChain_cost_zero_mem {Y : Scheme.{u}} [IsNoetherian Y]
    (Z : Closeds Y) (y : Y) (C : Distance.Chain Z y) (hC : C.cost = 0) : y ∈ Z := by
  have hlen : C.length = 0 := by
    rw [Distance.Chain.cost_eq] at hC
    omega
  have hvert : C.verticalCodim (0 : Fin (C.length + 1)) = 0 := by
    rw [Distance.Chain.cost_eq] at hC
    have hC' : ∀ i : Fin (C.length + 1),
        ((∑ j : Fin (C.length + 1), if i ≤ j then C.verticalCodim j else 0) -
          ∑ j : Fin C.length, if i.val ≤ j.val then C.bridgeCodim j else 0) = 0 := by
      simpa [hlen] using hC
    have hV : (∑ i : Fin C.length, C.verticalCodim i.succ) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hlen] at i
      exact Fin.elim0 i
    have hB : (∑ i : Fin C.length, C.bridgeCodim i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hlen] at i
      exact Fin.elim0 i
    have hz := hC' (0 : Fin (C.length + 1))
    simp [Fin.sum_univ_succ] at hz
    omega
  have hpc : pointCodim (C.lower_le_upper 0) = 0 := by
    exact hvert
  have hcodim : TopologicalSpace.codimBetween
      (_root_.toIrreducibleCloseds (C.lower 0))
      (_root_.toIrreducibleCloseds (C.upper 0))
      (toIrreducibleCloseds_le_iff_specializes.mpr
        (Y.le_iff_specializes.mp (C.lower_le_upper 0))) = 0 := by
    rw [← pointCodim_coe (C.lower_le_upper 0)]
    simp [hpc]
  have hmax : IsMax (⟨_root_.toIrreducibleCloseds (C.lower 0), le_rfl,
      toIrreducibleCloseds_le_iff_specializes.mpr
        (Y.le_iff_specializes.mp (C.lower_le_upper 0))⟩ :
      Set.Icc (_root_.toIrreducibleCloseds (C.lower 0))
        (_root_.toIrreducibleCloseds (C.upper 0))) := by
    unfold TopologicalSpace.codimBetween at hcodim
    rw [Order.coheight_eq_zero] at hcodim
    exact hcodim
  have heq : _root_.toIrreducibleCloseds (C.lower 0) =
      _root_.toIrreducibleCloseds (C.upper 0) := by
    have hsub : (⟨_root_.toIrreducibleCloseds (C.lower 0), le_rfl,
        toIrreducibleCloseds_le_iff_specializes.mpr
          (Y.le_iff_specializes.mp (C.lower_le_upper 0))⟩ :
        Set.Icc (_root_.toIrreducibleCloseds (C.lower 0))
          (_root_.toIrreducibleCloseds (C.upper 0))) ≤
      ⟨_root_.toIrreducibleCloseds (C.upper 0),
        toIrreducibleCloseds_le_iff_specializes.mpr
          (Y.le_iff_specializes.mp (C.lower_le_upper 0)), le_rfl⟩ := by
        change _root_.toIrreducibleCloseds (C.lower 0) ≤
          _root_.toIrreducibleCloseds (C.upper 0)
        exact toIrreducibleCloseds_le_iff_specializes.mpr
          (Y.le_iff_specializes.mp (C.lower_le_upper 0))
    exact congrArg Subtype.val (hmax.eq_of_le hsub)
  have hinsep : Inseparable (C.lower 0) (C.upper 0) :=
    toIrreducibleCloseds_eq_iff_inseparable.mp heq
  have hpoint : C.lower 0 = C.upper 0 := (inseparable_iff_eq.mp hinsep)
  have hmem : C.lower 0 ∈ Z := C.lower_zero_mem
  have hupper : C.upper 0 ∈ Z := by simpa [hpoint] using hmem
  have hlast : (Fin.last C.length : Fin (C.length + 1)) = 0 := by
    apply Fin.ext
    simp [hlen]
  have hupperlast : C.upper (Fin.last C.length) ∈ Z := by
    rw [hlast]
    exact hupper
  exact C.upper_last_eq ▸ hupperlast

/-- The distance from a point `y` to a closed subset `Z` of a Noetherian scheme is zero
exactly when `y ∈ Z`. -/
theorem distanceTo_eq_zero_iff {Y : Scheme.{u}} [IsNoetherian Y]
    (Z : Closeds Y) (y : Y) :
    Y.distanceTo Z y = 0 ↔ y ∈ Z := by
  constructor
  · intro hzero
    by_cases hconn : (connectedComponent y ∩ Z).Nonempty
    · obtain ⟨C, hC⟩ := exists_chain_cost_eq_distanceTo Y Z y hconn
      apply distanceChain_cost_zero_mem Z y C
      apply ENat.coe_inj.mp
      simpa using hC.trans hzero
    · have hempty : connectedComponent y ∩ Z = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hconn
      have htop : Y.distanceTo Z y = ⊤ :=
        (distanceTo_eq_top_iff Y Z y).mpr hempty
      exfalso
      rw [htop] at hzero
      simpa using hzero
  · intro hy
    let C : Distance.Chain Z y := Distance.Chain.ofPoints 0
      (fun _ ↦ y) (fun _ ↦ y)
      (by intro i; exact le_rfl)
      (by intro i; exact Fin.elim0 i)
      hy rfl
    have hC : C.cost = 0 := by
      simp [C, Distance.Chain.ofPoints, Distance.Chain.cost,
        Distance.Chain.verticalCodim, pointCodim, codimBetween_self_zero]
    rw [distanceTo_apply, ENat.sInf_eq_zero]
    exact ⟨C, by simpa [hC]⟩

/-- Every sublevel set of the distance to a closed subset of a Noetherian scheme is stable
under specialization. -/
theorem stableUnderSpecialization_distanceTo_le
    {Y : Scheme.{u}} [IsNoetherian Y] (Z : Closeds Y) (k : ℕ∞) :
    StableUnderSpecialization {y : Y | Y.distanceTo Z y ≤ k} := sorry

/-- At a point `z` of the reduced closure of `y` whose image lies in `Z`, the dimension of
the local ring of that closure is at least the distance from `y` to `Z`. -/
theorem distanceTo_le_ringKrullDim_pointClosure_stalk
    {Y : Scheme.{u}} [IsNoetherian Y] (Z : Closeds Y) (y : Y)
    (z : PointClosure.scheme y) (hz : (PointClosure.ι y) z ∈ Z) :
    (Y.distanceTo Z y : WithBot ℕ∞) ≤
      ringKrullDim ((PointClosure.scheme y).presheaf.stalk z) := sorry

/-- If `δ` is a dimension function on a Noetherian scheme and `δmax` is its maximum on
`Z`, then the distance to `Z` is bounded below by the nonnegative part of `δ y - δmax`. -/
theorem dimensionFunction_sub_max_le_distanceTo
    {Y : Scheme.{u}} [IsNoetherian Y] (Z : Closeds Y) (δ : Y → ℤ)
    [IsDimensionFunction δ] (δmax : ℤ)
    (hδmax : IsGreatest (δ '' (Z : Set Y)) δmax) (y : Y) :
    ((δ y - δmax).toNat : ℕ∞) ≤ Y.distanceTo Z y := sorry

/-- For the spectrum of a catenary Noetherian local ring, distance to the closed point
equals the dimension of the closure of the given point. -/
theorem distanceTo_closedPoint_eq_topologicalKrullDim_closure
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsCatenaryRing A] (y : PrimeSpectrum A) :
    (distanceTo (Spec (.of A))
        (⟨({IsLocalRing.closedPoint A} : Set (PrimeSpectrum A)),
          IsLocalRing.isClosed_singleton_closedPoint A⟩ : Closeds (Spec (.of A))) y :
      WithBot ℕ∞) =
      topologicalKrullDim (closure ({y} : Set (PrimeSpectrum A))) := sorry

/-- Restriction to an open subscheme of a Noetherian scheme can only increase the distance
to the restricted closed subset. -/
theorem distanceTo_le_open
    {Y : Scheme.{u}} [IsNoetherian Y] (Z : Closeds Y) (U : Y.Opens) (y : U) :
    Y.distanceTo Z (U.ι y) ≤
      @distanceTo U.toScheme (instIsNoetherianRestrictOfIsNoetherian U)
        (Z.preimage U.ι.continuous) y := sorry

/-- On a catenary Noetherian scheme, the distance of an immediate generalization of `y`
to `Z` is at most the distance of `y` to `Z` plus one. -/
theorem distanceTo_le_add_one_of_immediateSpecialization
    {Y : Scheme.{u}} [IsNoetherian Y] [CatenarySpace Y] (Z : Closeds Y)
    {y' y : Y} (h : IsImmediateSpecialization y' y) :
    Y.distanceTo Z y' ≤ Y.distanceTo Z y + 1 := sorry

/-- In a catenary Noetherian scheme, a zigzag with `k` immediate left specializations,
starting at a point of `Z`, ends at distance at most `k` from `Z`. -/
theorem distanceTo_le_of_specialization_pattern
    {Y : Scheme.{u}} [IsNoetherian Y] [CatenarySpace Y] (Z : Closeds Y) (k : ℕ)
    (y : Fin (k + 1) → Y) (y' : Fin k → Y) (hy0 : y 0 ∈ Z)
    (hleft : ∀ i : Fin k, IsImmediateSpecialization (y' i) (y i.castSucc))
    (hright : ∀ i : Fin k, y' i ⤳ y i.succ) :
    Y.distanceTo Z (y (Fin.last k)) ≤ k := by
  induction k with
  | zero =>
      have hy : y (Fin.last 0) ∈ Z := by
        simpa using hy0
      have hzero : Y.distanceTo Z (y (Fin.last 0)) = 0 :=
        distanceTo_eq_zero_iff Z (y (Fin.last 0)) |>.mpr hy
      simpa [hzero]
  | succ k ih =>
      let y₀ : Fin (k + 1) → Y := fun i ↦ y i.castSucc
      let y'₀ : Fin k → Y := fun i ↦ y' i.castSucc
      have hy₀ : y₀ 0 ∈ Z := by
        simpa [y₀] using hy0
      have hleft₀ : ∀ i : Fin k, IsImmediateSpecialization (y'₀ i) (y₀ i.castSucc) := by
        intro i
        simpa [y₀, y'₀] using hleft i.castSucc
      have hright₀ : ∀ i : Fin k, y'₀ i ⤳ y₀ i.succ := by
        intro i
        simpa [y₀, y'₀] using hright i.castSucc
      have hi : Y.distanceTo Z (y₀ (Fin.last k)) ≤ k :=
        ih y₀ y'₀ hy₀ hleft₀ hright₀
      have hstep :
          Y.distanceTo Z (y' (Fin.last k)) ≤ (k + 1 : ℕ∞) := by
        have h₁ := distanceTo_le_add_one_of_immediateSpecialization Z
          (hleft (Fin.last k))
        have hi' : Y.distanceTo Z (y (Fin.last k).castSucc) ≤ (k : ℕ∞) := by
          simpa [y₀] using hi
        exact h₁.trans (by simpa using add_le_add_right hi' 1)
      have hfinal := (stableUnderSpecialization_distanceTo_le Z (k + 1))
        (hright (Fin.last k)) hstep
      simpa using hfinal

end AlgebraicGeometry.Scheme
