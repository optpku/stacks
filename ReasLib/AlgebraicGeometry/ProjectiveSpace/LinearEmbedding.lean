/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.Data.Fin.VecNotation
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Over
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Nonconstant

/-!
# A linear embedding of the complex projective line into projective 5-space

This file constructs the scheme morphism
`ProjectiveSpace.scheme ℂ 1 ⟶ ProjectiveSpace.scheme ℂ 5` induced by the
coordinate substitution `(T 0, T 1, T 2, T 3, T 4, T 5) ↦ (X 0, X 1, 0, 0, 0, 0)`,
and records that it is a nonconstant morphism over `Spec ℂ`.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom

namespace AlgebraicGeometry.ProjectiveSpace.LinearEmbedding

/-- The linear substitution sending the six homogeneous coordinates of
`scheme ℂ 5` to `(X 0, X 1, 0, 0, 0, 0)` in the homogeneous coordinate ring of
`scheme ℂ 1`. -/
def coordinateImage : Fin (5 + 1) → MvPolynomial (Fin (1 + 1)) ℂ :=
  ![MvPolynomial.X 0, MvPolynomial.X 1, 0, 0, 0, 0]

/-- The substitution sends the first homogeneous coordinate to `X 0`. -/
theorem coordinateImage_zero : coordinateImage 0 = MvPolynomial.X 0 := sorry

/-- The substitution sends the second homogeneous coordinate to `X 1`. -/
theorem coordinateImage_one : coordinateImage 1 = MvPolynomial.X 1 := sorry

/-- Homogeneous coordinates of index at least `2` are sent to zero. -/
theorem coordinateImage_of_two_le {i : Fin (5 + 1)} (hi : 2 ≤ (i : ℕ)) :
    coordinateImage i = 0 := sorry

/-- The ungraded ring homomorphism `ℂ[T 0, …, T 5] →+* ℂ[X 0, X 1]` extending
`coordinateImage`. -/
def ringHom :
    MvPolynomial (Fin (5 + 1)) ℂ →+* MvPolynomial (Fin (1 + 1)) ℂ :=
  MvPolynomial.eval₂Hom (algebraMap ℂ (MvPolynomial (Fin (1 + 1)) ℂ)) coordinateImage

/-- `ringHom` evaluates variables according to `coordinateImage`. -/
theorem ringHom_X (i : Fin (5 + 1)) :
    ringHom (MvPolynomial.X i) = coordinateImage i := sorry

/-- `ringHom` preserves the standard homogeneous grading. -/
theorem ringHom_map_mem {d : ℕ} {x : MvPolynomial (Fin (5 + 1)) ℂ}
    (hx : x ∈ grading ℂ 5 d) : ringHom x ∈ grading ℂ 1 d := sorry

/-- The graded ring homomorphism inducing the linear embedding
`scheme ℂ 1 ⟶ scheme ℂ 5`. -/
def gradedHom : grading ℂ 5 →+*ᵍ grading ℂ 1 where
  toRingHom := ringHom
  map_mem := ringHom_map_mem

/-- The graded substitution sends the irrelevant ideal of the target coordinate
ring into the image of the source irrelevant ideal. -/
theorem gradedHom_irrelevant :
    HomogeneousIdeal.irrelevant (grading ℂ 1) ≤
      (HomogeneousIdeal.irrelevant (grading ℂ 5)).map gradedHom := sorry

/-- The scheme morphism `scheme ℂ 1 ⟶ scheme ℂ 5` induced by the linear
coordinate substitution. -/
def hom : scheme ℂ 1 ⟶ scheme ℂ 5 :=
  Proj.map gradedHom gradedHom_irrelevant

/-- `hom` is a morphism of schemes over `Spec ℂ`. -/
theorem hom_comp_toSpec : hom ≫ toSpec ℂ 5 = toSpec ℂ 1 := sorry

/-- The linear embedding `hom` is a nonconstant morphism of schemes. -/
theorem isNonconstant : hom.IsNonconstant := sorry

/-- The slice morphism over `Spec ℂ` associated to `hom`. -/
def homOver : schemeOver ℂ 1 ⟶ schemeOver ℂ 5 :=
  Over.homMk hom hom_comp_toSpec

/-- The underlying scheme morphism of `homOver` is `hom`. -/
theorem homOver_left : homOver.left = hom := sorry

end AlgebraicGeometry.ProjectiveSpace.LinearEmbedding
