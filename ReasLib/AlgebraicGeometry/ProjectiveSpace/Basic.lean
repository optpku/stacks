module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Standard projective spaces

Standard projective space over an affine base is constructed from the homogeneous grading on a
polynomial ring. Its canonical structure morphism and its restriction to affine opens are also
described.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry
namespace ProjectiveSpace

/-- The standard grading on `R[T_0, ..., T_n]`, used to model projective `n`-space over an
affine base ring `R` by `Proj`. -/
@[stacks 01JE "standard projective grading"]
abbrev grading (R : Type u) [CommRing R] (n : ℕ) :
    ℕ → Submodule R (MvPolynomial (Fin (n + 1)) R) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- The standard projective-space grading carries its canonical graded-ring structure.  The
instance head is restricted to `grading`, so other gradings on multivariable
polynomials remain available without an instance diamond. -/
@[stacks 01JE "standard projective grading instance"]
instance grading_gradedRing
    (R : Type u) [CommRing R] (n : ℕ) :
    GradedRing (grading R n) :=
  MvPolynomial.gradedAlgebra

/-- The standard projective `n`-space over an affine base ring `R`, realized as `Proj` of the
standard graded polynomial ring. -/
@[stacks 01JE "projective space"]
abbrev scheme (R : Type u) [CommRing R] (n : ℕ) : Scheme :=
  Proj (grading R n)

/-- The canonical constant-polynomial embedding into the degree-zero graded piece. -/
@[stacks 01JE "degree-zero constant embedding"]
noncomputable def degreeZeroC
    (R : Type u) [CommRing R] (n : ℕ) (r : R) :
    grading R n 0 :=
  ⟨MvPolynomial.C r, (MvPolynomial.mem_homogeneousSubmodule 0 _).2
    (@MvPolynomial.isHomogeneous_C (Fin (n + 1)) R _ r)⟩

/-- Constant coefficient followed by the degree-zero constant embedding is left inverse to the
degree-zero constant-coefficient map. -/
@[stacks 01JE "degree-zero constant embedding left inverse"]
theorem degreeZero_leftInverse
    (R : Type u) [CommRing R] (n : ℕ) :
    Function.LeftInverse (degreeZeroC R n)
      (fun p : grading R n 0 ↦ MvPolynomial.constantCoeff p.1) := sorry

/-- The degree-zero constant embedding is right inverse to the degree-zero
constant-coefficient map. -/
@[stacks 01JE "degree-zero constant embedding right inverse"]
theorem degreeZero_rightInverse
    (R : Type u) [CommRing R] (n : ℕ) :
    Function.RightInverse (degreeZeroC R n)
      (fun p : grading R n 0 ↦ MvPolynomial.constantCoeff p.1) := sorry

/-- Constant coefficient preserves multiplication on the degree-zero graded piece. -/
@[stacks 01JE "degree-zero constant coefficient multiplication"]
theorem degreeZero_map_mul
    (R : Type u) [CommRing R] (n : ℕ) (p q : grading R n 0) :
    MvPolynomial.constantCoeff (p * q).1 =
      MvPolynomial.constantCoeff p.1 * MvPolynomial.constantCoeff q.1 := sorry

/-- Constant coefficient preserves addition on the degree-zero graded piece. -/
@[stacks 01JE "degree-zero constant coefficient addition"]
theorem degreeZero_map_add
    (R : Type u) [CommRing R] (n : ℕ) (p q : grading R n 0) :
    MvPolynomial.constantCoeff (p + q).1 =
      MvPolynomial.constantCoeff p.1 + MvPolynomial.constantCoeff q.1 := sorry

/-- The degree-zero piece of the standard grading on `R[T_0, ..., T_n]` is canonically `R`,
via constant polynomials. -/
@[stacks 01JE "degree-zero ring equivalence"]
noncomputable def degreeZeroRingEquiv
    (R : Type u) [CommRing R] (n : ℕ) :
    grading R n 0 ≃+* R where
  toFun p := MvPolynomial.constantCoeff p.1
  invFun := degreeZeroC R n
  left_inv := degreeZero_leftInverse R n
  right_inv := degreeZero_rightInverse R n
  map_mul' := degreeZero_map_mul R n
  map_add' := degreeZero_map_add R n

/-- The canonical identification of the degree-zero affine base of the standard `Proj`
construction with `Spec R`. -/
@[stacks 01JE "degree-zero spectrum isomorphism"]
noncomputable def degreeZeroSpecIso
    (R : Type u) [CommRing R] (n : ℕ) :
    Spec (.of (grading R n 0)) ≅ Spec (.of R) :=
  (Scheme.Spec.mapIso
    (degreeZeroRingEquiv R n).toCommRingCatIso.op).symm

/-- The canonical structure morphism from the standard projective `n`-space over `R` to
`Spec R`. -/
@[stacks 01JE "projective-space structure morphism"]
abbrev toSpec (R : Type u) [CommRing R] (n : ℕ) :
    scheme R n ⟶ Spec (.of R) :=
  Proj.toSpecZero (grading R n) ≫ (degreeZeroSpecIso R n).hom

/-- The canonical map from the base ring to global sections of standard projective space. -/
@[stacks 01JE "projective-space global-sections comparison"]
noncomputable abbrev globalSectionsComparison
    (R : Type u) [CommRing R] (n : ℕ) :
    CommRingCat.of R ⟶ Scheme.Γ.obj (Opposite.op (scheme R n)) :=
  (Scheme.ΓSpecIso (.of R)).inv ≫ Scheme.Γ.map (toSpec R n).op

namespace globalSectionsComparison

/-- Pullback along the structure morphism identifies the base ring with global sections of
standard projective space. -/
@[stacks 01JE "global sections of projective space"]
theorem isIso (R : Type u) [CommRing R] (n : ℕ) :
    IsIso (globalSectionsComparison R n) := sorry

end globalSectionsComparison

section

variable {S : Scheme.{u}}

/-- The canonical map from the standard projective `n`-space over `Γ(S, U)` to the bundled
affine open subscheme `U ⊆ S`. -/
abbrev toAffineOpen (U : S.affineOpens) (n : ℕ) :
    scheme Γ(S, U) n ⟶ U.1.toScheme :=
  toSpec Γ(S, U) n ≫ U.2.isoSpec.inv

/-- The canonical map to an affine open when the open and its affineness proof are given
separately. -/
abbrev toAffineOpen_of_isAffineOpen (U : S.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    scheme Γ(S, U) n ⟶ U.toScheme :=
  toAffineOpen ⟨U, hU⟩ n

end

end ProjectiveSpace

/-- Deprecated root name for the standard projective-space grading. -/
@[deprecated ProjectiveSpace.grading (since := "2026-08-05")]
abbrev projectiveSpaceGrading (R : Type u) [CommRing R] (n : ℕ) :=
  ProjectiveSpace.grading R n

/-- Deprecated root name for standard projective space. -/
@[deprecated ProjectiveSpace.scheme (since := "2026-08-05")]
abbrev projectiveSpace (R : Type u) [CommRing R] (n : ℕ) :=
  ProjectiveSpace.scheme R n

/-- Deprecated root name for the structure morphism of standard projective space. -/
@[deprecated ProjectiveSpace.toSpec (since := "2026-08-05")]
abbrev projectiveSpaceToSpec (R : Type u) [CommRing R] (n : ℕ) :=
  ProjectiveSpace.toSpec R n

end AlgebraicGeometry
