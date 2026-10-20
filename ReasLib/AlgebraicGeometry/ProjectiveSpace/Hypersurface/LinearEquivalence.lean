/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hypersurface

/-!
# Degree-`d` hypersurfaces and projective-linear equivalence

This module defines degree predicates and projective-linear equivalence for closed
hypersurfaces in standard projective space.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme
open Matrix

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.Hypersurface

/-- A closed subscheme of `P^n` over `K` is a hypersurface of degree `d` if it is cut out
by a nonzero homogeneous form of degree `d`. -/
def IsOfDegree {K : Type u} [CommRing K] (n d : ℕ)
    (Z : (ProjectiveSpace.scheme K n).IdealSheafData) : Prop :=
  ∃ F : MvPolynomial (Fin (n + 1)) K,
    F ≠ 0 ∧ F ∈ ProjectiveSpace.grading K n d ∧ HasHomogeneousEquation n Z F

/-- A degree predicate is equivalent to the existence of its nonzero homogeneous equation. -/
theorem isOfDegree_iff {K : Type u} [CommRing K] {n d : ℕ}
    {Z : (ProjectiveSpace.scheme K n).IdealSheafData} :
    IsOfDegree n d Z ↔
      ∃ F : MvPolynomial (Fin (n + 1)) K,
        F ≠ 0 ∧ F ∈ ProjectiveSpace.grading K n d ∧ HasHomogeneousEquation n Z F := sorry

/-- A degree-`d` hypersurface has a nonzero homogeneous equation of degree `d`. -/
theorem exists_homogeneousEquation {K : Type u} [CommRing K] {n d : ℕ}
    {Z : (ProjectiveSpace.scheme K n).IdealSheafData} (hZ : IsOfDegree n d Z) :
    ∃ F : MvPolynomial (Fin (n + 1)) K,
      F ≠ 0 ∧ F ∈ ProjectiveSpace.grading K n d ∧ HasHomogeneousEquation n Z F := sorry

/-- Linear substitution of homogeneous coordinates by a matrix in `GL (n+1) K`. -/
def linearSubst {K : Type u} [CommRing K] (n : ℕ) (A : GL (Fin (n + 1)) K) :
    MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin (n + 1)) K :=
  MvPolynomial.aeval fun i =>
    Finset.univ.sum fun j : Fin (n + 1) => MvPolynomial.C (A i j) * MvPolynomial.X j

/-- Linear substitution by `A : GL (n+1) K` preserves the degree-`d` summand of the
standard grading. -/
theorem linearSubst_isHomogeneous {K : Type u} [CommRing K] {n d : ℕ}
    (A : GL (Fin (n + 1)) K) {F : MvPolynomial (Fin (n + 1)) K}
    (hF : F ∈ ProjectiveSpace.grading K n d) :
    linearSubst n A F ∈ ProjectiveSpace.grading K n d := sorry

/-- Two degree-`d` hypersurfaces in `P^n_K` are projectively linearly equivalent if some
invertible coordinate change carries one homogeneous equation to the other up to a
nonzero scalar. -/
def IsLinearEquivalent {K : Type u} [Field K] (n d : ℕ)
    (X Y : (ProjectiveSpace.scheme K n).IdealSheafData) : Prop :=
  ∃ (A : GL (Fin (n + 1)) K) (F G : MvPolynomial (Fin (n + 1)) K) (c : Kˣ),
    F ≠ 0 ∧ G ≠ 0 ∧
      F ∈ ProjectiveSpace.grading K n d ∧ G ∈ ProjectiveSpace.grading K n d ∧
        HasHomogeneousEquation n X F ∧ HasHomogeneousEquation n Y G ∧
          linearSubst n A F = MvPolynomial.C (c : K) * G

/-- Projective-linear equivalence is equivalent to the existence of an invertible coordinate
change and homogeneous equations related by a nonzero scalar. -/
theorem isLinearEquivalent_iff {K : Type u} [Field K] {n d : ℕ}
    {X Y : (ProjectiveSpace.scheme K n).IdealSheafData} :
    IsLinearEquivalent n d X Y ↔
      ∃ (A : GL (Fin (n + 1)) K) (F G : MvPolynomial (Fin (n + 1)) K) (c : Kˣ),
        F ≠ 0 ∧ G ≠ 0 ∧
          F ∈ ProjectiveSpace.grading K n d ∧ G ∈ ProjectiveSpace.grading K n d ∧
            HasHomogeneousEquation n X F ∧ HasHomogeneousEquation n Y G ∧
              linearSubst n A F = MvPolynomial.C (c : K) * G := sorry

/-- Projective-linear equivalence is reflexive on degree-`d` hypersurfaces. -/
theorem IsLinearEquivalent.refl {K : Type u} [Field K] {n d : ℕ}
    {Z : (ProjectiveSpace.scheme K n).IdealSheafData} (hZ : IsOfDegree n d Z) :
    IsLinearEquivalent n d Z Z := sorry

end AlgebraicGeometry.ProjectiveSpace.Hypersurface
