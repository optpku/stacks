/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.EnvelopeDescent
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernPolynomial.Newton
import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.Commutation
import Mathlib.Tactic.NoncommRing

@[expose] public section

open CategoryTheory
open scoped BigOperators DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass.Derived

/-- Projecting homogeneous products transfers commutativity from the full integer grading
of Chow cohomology to its nonnegative grading. -/
private theorem totalClass_homogeneous_commute
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : ChernClass.Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) (i j : ℕ) :
    Commute
      (ChernClass.homogeneous δ π i (totalClass δ π classes E hPerfect hDefined i))
      (ChernClass.homogeneous δ π j (totalClass δ π classes E hPerfect hDefined j)) := by
  let project : ChowCohomology.ring δ π → ChowCohomology.Nonnegative.ring δ π :=
    DFinsupp.comapDomain (fun n : ℕ ↦ (n : ℤ)) Int.ofNat_injective
  have project_mul (i j : ℕ)
      (c : ChowCohomology.Nonnegative.degree δ π i)
      (d : ChowCohomology.Nonnegative.degree δ π j) :
      project (DirectSum.of (ChowCohomology.degree δ π) (i : ℤ) c *
          DirectSum.of (ChowCohomology.degree δ π) (j : ℤ) d) =
        ChernClass.homogeneous δ π i c * ChernClass.homogeneous δ π j d := by
    simp only [ChernClass.homogeneous, DirectSum.of_mul_of]
    change project (DirectSum.of (ChowCohomology.degree δ π) ((i : ℤ) + (j : ℤ))
        (ChowCohomology.mul δ π c d)) =
      DirectSum.of (ChowCohomology.Nonnegative.degree δ π) (i + j)
        (show ChowCohomology.degree δ π ((i + j : ℕ) : ℤ) from
          (ChowCohomology.Nonnegative.degree_add i j) ▸ ChowCohomology.mul δ π c d)
    have cast_single {p q : ℤ} (h : p = q) (a : ChowCohomology.degree δ π p) :
        DirectSum.of (ChowCohomology.degree δ π) p a =
          DirectSum.of (ChowCohomology.degree δ π) q (h ▸ a) := by
      cases h
      rfl
    rw [cast_single (ChowCohomology.Nonnegative.degree_add i j)]
    exact DFinsupp.comapDomain_single (fun n : ℕ ↦ (n : ℤ)) Int.ofNat_injective (i + j) _
  have h := (Semigroup.mem_center_iff.mp
    (component_mem_center δ π classes E hPerfect hDefined i))
    (DirectSum.of (ChowCohomology.degree δ π) (j : ℤ)
      (totalClass δ π classes E hPerfect hDefined j))
  have hp := congrArg project h
  rw [project_mul, project_mul] at hp
  exact hp.symm

/-- The positive Newton classes of a perfect derived module with defined Chern classes satisfy
the integral Newton recurrence in its Chern classes. -/
theorem newtonClass_succ
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : ChernClass.Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) (n : ℕ) :
    ChernClass.homogeneous δ π (n + 1)
        (newtonClass δ π classes E hPerfect hDefined (n + 1)) =
      (∑ j ∈ Finset.range n, ((-1 : ℤ) ^ j) •
        (ChernClass.homogeneous δ π (j + 1)
            (totalClass δ π classes E hPerfect hDefined (j + 1)) *
          ChernClass.homogeneous δ π (n - j)
            (newtonClass δ π classes E hPerfect hDefined (n - j)))) +
        (((-1 : ℤ) ^ n * (n + 1 : ℕ)) •
          ChernClass.homogeneous δ π (n + 1)
            (totalClass δ π classes E hPerfect hDefined (n + 1))) := sorry

/-- The first Newton class of a perfect derived module with defined Chern classes equals its
first Chern class in the total nonnegative Chow-cohomology ring. -/
theorem newtonClass_one
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : ChernClass.Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) :
    ChernClass.homogeneous δ π 1 (newtonClass δ π classes E hPerfect hDefined 1) =
      ChernClass.homogeneous δ π 1 (totalClass δ π classes E hPerfect hDefined 1) := by
  simpa using newtonClass_succ δ π classes E hPerfect hDefined 0

/-- The second Newton class of a perfect derived module with defined Chern classes is
`c₁(E) ^ 2 - 2 • c₂(E)` in the total nonnegative Chow-cohomology ring. -/
theorem newtonClass_two
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : ChernClass.Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) :
    ChernClass.homogeneous δ π 2 (newtonClass δ π classes E hPerfect hDefined 2) =
      ChernClass.homogeneous δ π 1 (totalClass δ π classes E hPerfect hDefined 1) ^ 2 -
        2 • ChernClass.homogeneous δ π 2
          (totalClass δ π classes E hPerfect hDefined 2) := by
  simpa [Finset.sum_range_succ, newtonClass_one, pow_two, sub_eq_add_neg] using
    newtonClass_succ δ π classes E hPerfect hDefined 1

/-- The third Newton class of a perfect derived module with defined Chern classes is
`c₁(E) ^ 3 - 3 • (c₁(E) * c₂(E)) + 3 • c₃(E)` in the total nonnegative
Chow-cohomology ring. -/
theorem newtonClass_three
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : ChernClass.Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) :
    ChernClass.homogeneous δ π 3 (newtonClass δ π classes E hPerfect hDefined 3) =
      ChernClass.homogeneous δ π 1 (totalClass δ π classes E hPerfect hDefined 1) ^ 3 -
        3 • (ChernClass.homogeneous δ π 1
            (totalClass δ π classes E hPerfect hDefined 1) *
          ChernClass.homogeneous δ π 2
            (totalClass δ π classes E hPerfect hDefined 2)) +
        3 • ChernClass.homogeneous δ π 3
          (totalClass δ π classes E hPerfect hDefined 3) := by
  have h := newtonClass_succ δ π classes E hPerfect hDefined 2
  simp [Finset.sum_range_succ, newtonClass_one, newtonClass_two] at h
  rw [h]
  noncomm_ring [(totalClass_homogeneous_commute δ π classes E hPerfect hDefined 1 2).eq.symm]

/-- The fourth Newton class of a perfect derived module with defined Chern classes is
`c₁(E) ^ 4 - 4 • (c₁(E) ^ 2 * c₂(E)) + 4 • (c₁(E) * c₃(E)) +
2 • c₂(E) ^ 2 - 4 • c₄(E)` in the total nonnegative Chow-cohomology ring. -/
theorem newtonClass_four
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : ChernClass.Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) :
    ChernClass.homogeneous δ π 4 (newtonClass δ π classes E hPerfect hDefined 4) =
      ChernClass.homogeneous δ π 1 (totalClass δ π classes E hPerfect hDefined 1) ^ 4 -
        4 • (ChernClass.homogeneous δ π 1
            (totalClass δ π classes E hPerfect hDefined 1) ^ 2 *
          ChernClass.homogeneous δ π 2
            (totalClass δ π classes E hPerfect hDefined 2)) +
        4 • (ChernClass.homogeneous δ π 1
            (totalClass δ π classes E hPerfect hDefined 1) *
          ChernClass.homogeneous δ π 3
            (totalClass δ π classes E hPerfect hDefined 3)) +
        2 • ChernClass.homogeneous δ π 2
            (totalClass δ π classes E hPerfect hDefined 2) ^ 2 -
        4 • ChernClass.homogeneous δ π 4
          (totalClass δ π classes E hPerfect hDefined 4) := by
  have h := newtonClass_succ δ π classes E hPerfect hDefined 3
  simp [Finset.sum_range_succ, newtonClass_one, newtonClass_two, newtonClass_three] at h
  rw [h]
  noncomm_ring [(totalClass_homogeneous_commute δ π classes E hPerfect hDefined 1 2).eq.symm,
    (totalClass_homogeneous_commute δ π classes E hPerfect hDefined 1 2).symm.left_comm,
    (totalClass_homogeneous_commute δ π classes E hPerfect hDefined 1 3).eq.symm]

/-- The degree-`p` Chern character of a perfect derived module with defined Chern classes is
its rationalized Newton class divided by `p!`. -/
theorem character_apply
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : ChernClass.Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) (p : ℕ) :
    character δ π classes E hPerfect hDefined p =
      TensorProduct.tmul ℤ (newtonClass δ π classes E hPerfect hDefined p)
        ((p.factorial : ℚ)⁻¹) := by
  rfl

/-- The degree-zero Chern character of a perfect derived module with defined Chern classes is
its rationalized degree-zero Newton class, which records the virtual rank. -/
theorem character_zero
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : ChernClass.Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) :
    character δ π classes E hPerfect hDefined 0 =
      TensorProduct.tmul ℤ (newtonClass δ π classes E hPerfect hDefined 0) 1 := by
  simpa using character_apply δ π classes E hPerfect hDefined 0

end AlgebraicGeometry.ChernClass.Derived
