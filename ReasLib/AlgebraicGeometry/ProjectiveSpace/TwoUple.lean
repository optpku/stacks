/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import ReasLib.Algebra.Module.Graded.HomogeneousMap
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic
public import ReasLib.RingTheory.MvPolynomial.Finite
import Mathlib.Tactic.FinCases

/-!
# 2-uple embedding of the projective plane

The six quadratic monomials define the 2-uple embedding
`ProjectiveSpace.scheme k 2 ⟶ ProjectiveSpace.scheme k 5`, its associated substitution
homomorphism, and the degree-`d` pieces of the homogeneous ideal of its image.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.TwoUple

/-- The six quadratic monomials `a₀ ^ 2`, `a₀ * a₁`, `a₀ * a₂`, `a₁ ^ 2`, `a₁ * a₂`, `a₂ ^ 2`
in that order, as coordinates of the 2-uple embedding of the projective plane. -/
def monomial (k : Type u) [CommRing k] :
    Fin (5 + 1) → MvPolynomial (Fin (2 + 1)) k :=
  ![MvPolynomial.X 0 ^ 2, MvPolynomial.X 0 * MvPolynomial.X 1, MvPolynomial.X 0 * MvPolynomial.X 2,
    MvPolynomial.X 1 ^ 2, MvPolynomial.X 1 * MvPolynomial.X 2, MvPolynomial.X 2 ^ 2]

/-- The coordinate list of the 2-uple embedding consists of the six quadratic monomials. -/
theorem monomial_apply (k : Type u) [CommRing k] :
    monomial k =
      ![MvPolynomial.X 0 ^ 2, MvPolynomial.X 0 * MvPolynomial.X 1,
        MvPolynomial.X 0 * MvPolynomial.X 2, MvPolynomial.X 1 ^ 2,
        MvPolynomial.X 1 * MvPolynomial.X 2, MvPolynomial.X 2 ^ 2] := rfl

/-- Each 2-uple coordinate is homogeneous of degree `2`. -/
theorem monomial_isHomogeneous {k : Type u} [CommRing k] (i : Fin (5 + 1)) :
    (monomial k i).IsHomogeneous 2 := by
  fin_cases i
  · exact MvPolynomial.isHomogeneous_X_pow 0 2
  · exact (MvPolynomial.isHomogeneous_X k 0).mul (MvPolynomial.isHomogeneous_X k 1)
  · exact (MvPolynomial.isHomogeneous_X k 0).mul (MvPolynomial.isHomogeneous_X k 2)
  · exact MvPolynomial.isHomogeneous_X_pow 1 2
  · exact (MvPolynomial.isHomogeneous_X k 1).mul (MvPolynomial.isHomogeneous_X k 2)
  · exact MvPolynomial.isHomogeneous_X_pow 2 2

/-- Substitution of the 2-uple quadrics, as a `k`-algebra map
`k[T₀, …, T₅] →ₐ[k] k[a₀, a₁, a₂]`. -/
def subst (k : Type u) [CommRing k] :
    MvPolynomial (Fin (5 + 1)) k →ₐ[k] MvPolynomial (Fin (2 + 1)) k :=
  MvPolynomial.aeval (monomial k)

/-- Substitution evaluates variables to the corresponding 2-uple quadrics. -/
theorem subst_X {k : Type u} [CommRing k] (i : Fin (5 + 1)) :
    subst k (MvPolynomial.X i) = monomial k i :=
  MvPolynomial.aeval_X (monomial k) i

/-- Substitution sends a degree-`d` form to a degree-`2 * d` form. -/
theorem subst_isHomogeneous {k : Type u} [CommRing k] {d : ℕ}
    {f : MvPolynomial (Fin (5 + 1)) k} (hf : f.IsHomogeneous d) :
    (subst k f).IsHomogeneous (2 * d) :=
  hf.aeval (monomial k) monomial_isHomogeneous

/-- The kernel of 2-uple substitution is a homogeneous ideal for the standard grading on
`k[T₀, …, T₅]`. -/
theorem homogeneousIdeal_isHomogeneous (k : Type u) [CommRing k] :
    (RingHom.ker (subst k)).IsHomogeneous (ProjectiveSpace.grading k 5) := by
  let f : GradedModule.MapsTo k (ProjectiveSpace.grading k 5)
      (ProjectiveSpace.grading k 2) (fun d ↦ 2 * d) :=
    ⟨(subst k).toLinearMap, fun _ _ hf ↦ subst_isHomogeneous hf⟩
  exact GradedModule.MapsTo.ker_isHomogeneous f
    (mul_right_injective₀ (by decide : (2 : ℕ) ≠ 0))

/-- The homogeneous ideal of the 2-uple image, realized as the kernel of substitution of the
six quadratic monomials. -/
def homogeneousIdeal (k : Type u) [CommRing k] :
    HomogeneousIdeal (ProjectiveSpace.grading k 5) where
  toSubmodule := RingHom.ker (subst k)
  is_homogeneous' := homogeneousIdeal_isHomogeneous k

/-- The underlying ideal of `homogeneousIdeal` is the kernel of 2-uple substitution. -/
theorem homogeneousIdeal_toIdeal (k : Type u) [CommRing k] :
    (homogeneousIdeal k).toIdeal = RingHom.ker (subst k) := rfl

/-- Membership in the 2-uple homogeneous ideal is vanishing under substitution. -/
theorem mem_homogeneousIdeal_iff {k : Type u} [CommRing k]
    {f : MvPolynomial (Fin (5 + 1)) k} :
    f ∈ homogeneousIdeal k ↔ subst k f = 0 := Iff.rfl

/-- Substituting the 2-uple quadrics into a degree-`d` form yields a degree-`2 * d` form. -/
theorem restriction_mem {k : Type u} [CommRing k] {d : ℕ}
    (f : ProjectiveSpace.grading k 5 d) :
    subst k f ∈ ProjectiveSpace.grading k 2 (2 * d) :=
  subst_isHomogeneous f.property

/-- Restriction of degree-`d` forms along the 2-uple substitution, landing in degree `2 * d`. -/
def restriction (k : Type u) [CommRing k] (d : ℕ) :
    ProjectiveSpace.grading k 5 d →ₗ[k] ProjectiveSpace.grading k 2 (2 * d) :=
  LinearMap.codRestrict (ProjectiveSpace.grading k 2 (2 * d))
    ((subst k).toLinearMap.comp (ProjectiveSpace.grading k 5 d).subtype) restriction_mem

/-- Restriction acts by 2-uple substitution on the underlying polynomial. -/
theorem restriction_apply {k : Type u} [CommRing k] {d : ℕ}
    (f : ProjectiveSpace.grading k 5 d) :
    (restriction k d f : MvPolynomial (Fin (2 + 1)) k) = subst k f := rfl

/-- Every degree-`2 * d` form on the projective plane is the restriction of some degree-`d`
form on projective 5-space. -/
theorem restriction_surjective {k : Type u} [CommRing k] (d : ℕ) :
    Function.Surjective (restriction k d) := by
  have hquad : (ProjectiveSpace.grading k 5 1).map (subst k).toLinearMap =
      ProjectiveSpace.grading k 2 2 := by
    dsimp only [ProjectiveSpace.grading]
    apply le_antisymm
    · rintro _ ⟨f, hf, rfl⟩
      exact subst_isHomogeneous hf
    · rw [← MvPolynomial.homogeneousSubmodule_one_pow (R := k) (n := 2), pow_two,
        MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.span_mul_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
      have hX (a : Fin (5 + 1)) : monomial k a ∈
          (ProjectiveSpace.grading k 5 1).map (subst k).toLinearMap :=
        ⟨MvPolynomial.X a, MvPolynomial.isHomogeneous_X k a, subst_X a⟩
      fin_cases i <;> fin_cases j
      · simpa [monomial, pow_two] using hX 0
      · exact hX 1
      · exact hX 2
      · change (MvPolynomial.X 1 * MvPolynomial.X 0 : MvPolynomial (Fin (2 + 1)) k) ∈ _
        rw [mul_comm]
        exact hX 1
      · simpa [monomial, pow_two] using hX 3
      · exact hX 4
      · change (MvPolynomial.X 2 * MvPolynomial.X 0 : MvPolynomial (Fin (2 + 1)) k) ∈ _
        rw [mul_comm]
        exact hX 2
      · change (MvPolynomial.X 2 * MvPolynomial.X 1 : MvPolynomial (Fin (2 + 1)) k) ∈ _
        rw [mul_comm]
        exact hX 4
      · simpa [monomial, pow_two] using hX 5
  have hmap : (ProjectiveSpace.grading k 5 d).map (subst k).toLinearMap =
      ProjectiveSpace.grading k 2 (2 * d) := by
    calc
      (ProjectiveSpace.grading k 5 d).map (subst k).toLinearMap =
          ((ProjectiveSpace.grading k 5 1) ^ d).map (subst k).toLinearMap := by
        simp only [ProjectiveSpace.grading, MvPolynomial.homogeneousSubmodule_one_pow]
      _ = ((ProjectiveSpace.grading k 5 1).map (subst k).toLinearMap) ^ d :=
        Submodule.map_pow _ (subst k) d
      _ = (ProjectiveSpace.grading k 2 2) ^ d := by rw [hquad]
      _ = ((ProjectiveSpace.grading k 2 1) ^ 2) ^ d := by
        simp only [ProjectiveSpace.grading, MvPolynomial.homogeneousSubmodule_one_pow]
      _ = ProjectiveSpace.grading k 2 (2 * d) := by
        dsimp only [ProjectiveSpace.grading]
        rw [← pow_mul, MvPolynomial.homogeneousSubmodule_one_pow]
  intro f
  have hf : (f : MvPolynomial (Fin (2 + 1)) k) ∈
      (ProjectiveSpace.grading k 5 d).map (subst k).toLinearMap := by
    rw [hmap]
    exact f.property
  obtain ⟨g, hg, hgf⟩ := hf
  exact ⟨⟨g, hg⟩, Subtype.ext hgf⟩

/-- The degree-`d` piece of the homogeneous ideal of the 2-uple image, as the kernel of
restriction. -/
def idealDegree (k : Type u) [CommRing k] (d : ℕ) :
    Submodule k (ProjectiveSpace.grading k 5 d) :=
  LinearMap.ker (restriction k d)

/-- Membership in `idealDegree k d` is vanishing of the underlying degree-`d` form under
2-uple substitution. -/
theorem mem_idealDegree_iff {k : Type u} [CommRing k] {d : ℕ}
    (f : ProjectiveSpace.grading k 5 d) :
    f ∈ idealDegree k d ↔ subst k f = 0 := by
  change restriction k d f = 0 ↔ subst k f = 0
  exact Subtype.ext_iff

/-- The degree-`d` kernel is the degree-`d` piece of `homogeneousIdeal`. -/
theorem mem_idealDegree_iff_mem_homogeneousIdeal {k : Type u} [CommRing k] {d : ℕ}
    (f : ProjectiveSpace.grading k 5 d) :
    f ∈ idealDegree k d ↔
      (f : MvPolynomial (Fin (5 + 1)) k) ∈ homogeneousIdeal k := by
  rw [mem_idealDegree_iff, mem_homogeneousIdeal_iff]

/-- Rank-nullity for 2-uple restriction: the dimensions of `idealDegree k d` and of the
degree-`2 * d` forms on the plane add to the dimension of the degree-`d` forms on
projective 5-space. -/
theorem finrank_idealDegree_add {k : Type u} [Field k] (d : ℕ) :
    Module.finrank k (idealDegree k d) + (2 + 1).multichoose (2 * d) =
      (5 + 1).multichoose d := by
  letI : Module.Finite k (ProjectiveSpace.grading k 5 d) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg _ _ d)
  have h := (restriction k d).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (restriction_surjective d), finrank_top,
    MvPolynomial.homogeneousSubmodule.finrank_fin,
    MvPolynomial.homogeneousSubmodule.finrank_fin, add_comm] at h
  exact h

/-- Over an algebraically closed field, the dimension of the degree-`d` piece of the
homogeneous ideal of the 2-uple image is the number of degree-`d` monomials in six variables
minus the number of degree-`2 * d` monomials in three variables. -/
theorem finrank_idealDegree {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ) :
    Module.finrank k (idealDegree k d) =
      (5 + 1).multichoose d - (2 + 1).multichoose (2 * d) :=
  Nat.eq_sub_of_add_eq (finrank_idealDegree_add d)

end AlgebraicGeometry.ProjectiveSpace.TwoUple
