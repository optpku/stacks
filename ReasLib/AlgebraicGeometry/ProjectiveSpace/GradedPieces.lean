module

public import ReasLib.Algebra.Module.Graded.NatToInt
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Integral graded pieces of standard projective space

This leaf owns the integer-indexed homogeneous pieces of the standard
polynomial grading used for projective space. Negative degrees are represented
by the zero submodule, which is the form needed by projective-space twist
cohomology statements.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry
namespace ProjectiveSpace

/-- The integer degree-`d` homogeneous piece of the standard polynomial grading; negative
degrees are represented by the zero submodule. This is the projective-space specialization of
the generic natural-to-integer grading extension. -/
@[stacks 01XT "integer homogeneous pieces used by projective-space cohomology"]
abbrev gradedPiece
    (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    Submodule R (MvPolynomial (Fin (n + 1)) R) :=
  DirectSum.Decomposition.natToIntGrading (grading R n) d

/-- In nonnegative degree, `gradedPiece` is the corresponding homogeneous submodule of the
standard grading. -/
@[stacks 01XT "nonnegative projective-space homogeneous piece"]
theorem gradedPiece_of_nonneg
    (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (hd : 0 ≤ d) :
    gradedPiece R n d = grading R n d.toNat := sorry

/-- In negative degree, `gradedPiece` is zero. -/
@[stacks 01XT "negative projective-space homogeneous piece"]
theorem gradedPiece_of_neg
    (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (hd : ¬ 0 ≤ d) :
    gradedPiece R n d = ⊥ := sorry

/-- The `R`-linear dual of the graded piece appearing in top cohomology of the twist by degree
`d`. -/
@[stacks 01XT "projective-space top-cohomology dual piece"]
abbrev topCohomologyDual
    (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :=
  gradedPiece R n (-((n : ℤ) + 1) - d) →ₗ[R] R

/-- Multiplication by a homogeneous polynomial of degree `m` sends the degree-`d` integer graded
piece into degree `d + m`. -/
@[stacks 01XV "multiplication on projective-space homogeneous pieces"]
theorem mul_mem_gradedPiece
    (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (m : ℕ)
    (f g : MvPolynomial (Fin (n + 1)) R)
    (hf : f ∈ grading R n m)
    (hg : g ∈ gradedPiece R n d) :
    f * g ∈ gradedPiece R n (d + (m : ℤ)) := sorry

/-- Multiplication by a homogeneous polynomial of degree `m` is the `R`-linear map from the
degree-`d` integer graded piece to the degree-`d + m` integer graded piece. -/
@[stacks 01XV "multiplication map on integer projective-space pieces"]
def mulMap
    (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (m : ℕ)
    (f : MvPolynomial (Fin (n + 1)) R)
    (hf : f ∈ grading R n m) :
    gradedPiece R n d →ₗ[R] gradedPiece R n (d + (m : ℤ)) where
  toFun g :=
    ⟨f * g.1, mul_mem_gradedPiece R n d m f g.1 hf g.2⟩
  map_add' := sorry
  map_smul' := sorry

/-- Multiplication by a degree-`m` polynomial sends the source degree of the top-dual piece for
`d + m` to the source degree of the top-dual piece for `d`. -/
@[stacks 01XV "top-dual multiplication membership"]
theorem topMul_mem
    (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (m : ℕ)
    (f : MvPolynomial (Fin (n + 1)) R)
    (hf : f ∈ grading R n m)
    (g : gradedPiece R n (-((n : ℤ) + 1) - (d + (m : ℤ)))) :
    f * g.1 ∈ gradedPiece R n (-((n : ℤ) + 1) - d) := sorry

/-- Multiplication by a degree-`m` polynomial on the degree appearing in the top-dual piece of
the twist by `d + m`, with its target rewritten as the top-dual degree for `d`. -/
@[stacks 01XV "top-dual multiplication source map"]
def topMulMap
    (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (m : ℕ)
    (f : MvPolynomial (Fin (n + 1)) R)
    (hf : f ∈ grading R n m) :
    gradedPiece R n (-((n : ℤ) + 1) - (d + (m : ℤ))) →ₗ[R]
      gradedPiece R n (-((n : ℤ) + 1) - d) where
  toFun g :=
    ⟨f * g.1, topMul_mem R n d m f hf g⟩
  map_add' := sorry
  map_smul' := sorry

/-- The contragredient action of a homogeneous polynomial on the top-cohomology dual pieces.
It is the dual map of `topMulMap`, so downstream statements need no ad hoc membership proof. -/
@[stacks 01XV "contragredient multiplication on top-cohomology dual pieces"]
abbrev mulDual
    (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (m : ℕ)
    (f : MvPolynomial (Fin (n + 1)) R)
    (hf : f ∈ grading R n m) :
    topCohomologyDual R n d →ₗ[R] topCohomologyDual R n (d + (m : ℤ)) :=
  (topMulMap R n d m f hf).dualMap

/-- Evaluation formula for the contragredient multiplication map. -/
@[simp, stacks 01XV "evaluation of contragredient multiplication"]
theorem mulDual_apply
    (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (m : ℕ)
    (f : MvPolynomial (Fin (n + 1)) R)
    (hf : f ∈ grading R n m)
    (φ : topCohomologyDual R n d)
    (g : gradedPiece R n (-((n : ℤ) + 1) - (d + (m : ℤ)))) :
    mulDual R n d m f hf φ g = φ ⟨f * g.1, topMul_mem R n d m f hf g⟩ := sorry

end ProjectiveSpace
end AlgebraicGeometry

/- The root spellings remain only as a migration facade for Chapter 30 and older downstream
files.  The definitions above are the canonical owners. -/

/-- Deprecated root spelling for `ProjectiveSpace.gradedPiece`; use the namespaced owner. -/
@[deprecated AlgebraicGeometry.ProjectiveSpace.gradedPiece (since := "2026-08-05")]
abbrev AlgebraicGeometry.projectiveSpaceGradedPiece
    (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    Submodule R (MvPolynomial (Fin (n + 1)) R) :=
  AlgebraicGeometry.ProjectiveSpace.gradedPiece R n d

/-- Deprecated root spelling for `ProjectiveSpace.topCohomologyDual`; use the namespaced owner. -/
@[deprecated AlgebraicGeometry.ProjectiveSpace.topCohomologyDual (since := "2026-08-05")]
abbrev AlgebraicGeometry.projectiveSpaceTopCohomologyDual
    (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :=
  AlgebraicGeometry.ProjectiveSpace.topCohomologyDual R n d
