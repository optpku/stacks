module

public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic
public import ReasLib.RingTheory.MvPolynomial.Finite

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
        MvPolynomial.X 1 * MvPolynomial.X 2, MvPolynomial.X 2 ^ 2] := sorry

/-- Each 2-uple coordinate is homogeneous of degree `2`. -/
theorem monomial_isHomogeneous {k : Type u} [CommRing k] (i : Fin (5 + 1)) :
    (monomial k i).IsHomogeneous 2 := sorry

/-- Substitution of the 2-uple quadrics, as a `k`-algebra map
`k[T₀, …, T₅] →ₐ[k] k[a₀, a₁, a₂]`. -/
def subst (k : Type u) [CommRing k] :
    MvPolynomial (Fin (5 + 1)) k →ₐ[k] MvPolynomial (Fin (2 + 1)) k :=
  MvPolynomial.aeval (monomial k)

/-- Substitution evaluates variables to the corresponding 2-uple quadrics. -/
theorem subst_X {k : Type u} [CommRing k] (i : Fin (5 + 1)) :
    subst k (MvPolynomial.X i) = monomial k i := sorry

/-- Substitution sends a degree-`d` form to a degree-`2 * d` form. -/
theorem subst_isHomogeneous {k : Type u} [CommRing k] {d : ℕ}
    {f : MvPolynomial (Fin (5 + 1)) k} (hf : f.IsHomogeneous d) :
    (subst k f).IsHomogeneous (2 * d) := sorry

/-- The kernel of 2-uple substitution is a homogeneous ideal for the standard grading on
`k[T₀, …, T₅]`. -/
theorem homogeneousIdeal_isHomogeneous (k : Type u) [CommRing k] :
    (RingHom.ker (subst k)).IsHomogeneous (ProjectiveSpace.grading k 5) := sorry

/-- The homogeneous ideal of the 2-uple image, realized as the kernel of substitution of the
six quadratic monomials. -/
def homogeneousIdeal (k : Type u) [CommRing k] :
    HomogeneousIdeal (ProjectiveSpace.grading k 5) where
  toSubmodule := RingHom.ker (subst k)
  is_homogeneous' := homogeneousIdeal_isHomogeneous k

/-- The underlying ideal of `homogeneousIdeal` is the kernel of 2-uple substitution. -/
theorem homogeneousIdeal_toIdeal (k : Type u) [CommRing k] :
    (homogeneousIdeal k).toIdeal = RingHom.ker (subst k) := sorry

/-- Membership in the 2-uple homogeneous ideal is vanishing under substitution. -/
theorem mem_homogeneousIdeal_iff {k : Type u} [CommRing k]
    {f : MvPolynomial (Fin (5 + 1)) k} :
    f ∈ homogeneousIdeal k ↔ subst k f = 0 := sorry

/-- Substituting the 2-uple quadrics into a degree-`d` form yields a degree-`2 * d` form. -/
theorem restriction_mem {k : Type u} [CommRing k] {d : ℕ}
    (f : ProjectiveSpace.grading k 5 d) :
    subst k f ∈ ProjectiveSpace.grading k 2 (2 * d) := sorry

/-- Restriction of degree-`d` forms along the 2-uple substitution, landing in degree `2 * d`. -/
def restriction (k : Type u) [CommRing k] (d : ℕ) :
    ProjectiveSpace.grading k 5 d →ₗ[k] ProjectiveSpace.grading k 2 (2 * d) :=
  LinearMap.codRestrict (ProjectiveSpace.grading k 2 (2 * d))
    ((subst k).toLinearMap.comp (ProjectiveSpace.grading k 5 d).subtype) restriction_mem

/-- Restriction acts by 2-uple substitution on the underlying polynomial. -/
theorem restriction_apply {k : Type u} [CommRing k] {d : ℕ}
    (f : ProjectiveSpace.grading k 5 d) :
    (restriction k d f : MvPolynomial (Fin (2 + 1)) k) = subst k f := sorry

/-- Every degree-`2 * d` form on the projective plane is the restriction of some degree-`d`
form on projective 5-space. -/
theorem restriction_surjective {k : Type u} [CommRing k] (d : ℕ) :
    Function.Surjective (restriction k d) := sorry

/-- The degree-`d` piece of the homogeneous ideal of the 2-uple image, as the kernel of
restriction. -/
def idealDegree (k : Type u) [CommRing k] (d : ℕ) :
    Submodule k (ProjectiveSpace.grading k 5 d) :=
  LinearMap.ker (restriction k d)

/-- Membership in `idealDegree k d` is vanishing of the underlying degree-`d` form under
2-uple substitution. -/
theorem mem_idealDegree_iff {k : Type u} [CommRing k] {d : ℕ}
    (f : ProjectiveSpace.grading k 5 d) :
    f ∈ idealDegree k d ↔ subst k f = 0 := sorry

/-- The degree-`d` kernel is the degree-`d` piece of `homogeneousIdeal`. -/
theorem mem_idealDegree_iff_mem_homogeneousIdeal {k : Type u} [CommRing k] {d : ℕ}
    (f : ProjectiveSpace.grading k 5 d) :
    f ∈ idealDegree k d ↔
      (f : MvPolynomial (Fin (5 + 1)) k) ∈ homogeneousIdeal k := sorry

/-- Rank-nullity for 2-uple restriction: the dimensions of `idealDegree k d` and of the
degree-`2 * d` forms on the plane add to the dimension of the degree-`d` forms on
projective 5-space. -/
theorem finrank_idealDegree_add {k : Type u} [Field k] (d : ℕ) :
    Module.finrank k (idealDegree k d) + (2 + 1).multichoose (2 * d) =
      (5 + 1).multichoose d := sorry

/-- Over an algebraically closed field, the dimension of the degree-`d` piece of the
homogeneous ideal of the 2-uple image is the number of degree-`d` monomials in six variables
minus the number of degree-`2 * d` monomials in three variables. -/
theorem finrank_idealDegree {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ) :
    Module.finrank k (idealDegree k d) =
      (5 + 1).multichoose d - (2 + 1).multichoose (2 * d) := sorry

end AlgebraicGeometry.ProjectiveSpace.TwoUple
