/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# The projective spectrum of a standard graded polynomial ring

The standard grading on a univariate polynomial ring identifies its degree-zero
piece with the coefficient ring and gives the canonical Proj-to-Spec morphism.
-/

@[expose] public section

open scoped DirectSum
open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.PolynomialProj

variable (A : Type u) [CommRing A]

/-- The standard grading on `A[X]`, in which `X` has degree one. -/
abbrev standardGrading (n : ℕ) : Submodule A (Polynomial A) :=
  Submodule.map (Polynomial.toFinsuppIsoLinear A).symm.toLinearMap
    (AddMonoidAlgebra.grade A n)

/-- The standard polynomial grading is multiplicative with respect to degrees. -/
instance standardGrading_grading : SetLike.GradedMonoid (standardGrading A) := sorry

/-- The standard polynomial grading is an internal direct-sum decomposition. -/
theorem standardGrading_isInternal : DirectSum.IsInternal (standardGrading A) := by
    let e := Polynomial.toFinsuppIsoLinear A
    let o := Submodule.orderIsoMapComap e.symm
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    have h := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top
      (AddMonoidAlgebra.grade A : ℕ → Submodule A (AddMonoidAlgebra A ℕ))).mp
      (AddMonoidAlgebra.grade.isInternal (R := A) (ι := ℕ))
    refine ⟨?_, ?_⟩
    · rw [show standardGrading A = o ∘ AddMonoidAlgebra.grade A by
        funext n; rfl]
      exact (iSupIndep_map_orderIso_iff o).mpr h.1
    · rw [show standardGrading A = o ∘ AddMonoidAlgebra.grade A by
        funext n; rfl]
      change (⨆ i, o (AddMonoidAlgebra.grade A i)) = ⊤
      exact (o.map_iSup (AddMonoidAlgebra.grade A)).symm.trans
        ((congrArg o h.2).trans o.map_top)

/-- The standard polynomial grading equips the polynomial ring with a graded-algebra structure. -/
instance standardGrading_gradedAlgebra : GradedAlgebra (standardGrading A) :=
  DirectSum.IsInternal.gradedAlgebra (standardGrading_isInternal A)

/-- The coefficient and constant-polynomial maps satisfy the degree-zero ring laws. -/
theorem degreeZeroRingEquiv_laws :
    (∀ a : A, Polynomial.C a ∈ standardGrading A 0) ∧
      (∀ x : standardGrading A 0, Polynomial.C (x.1.coeff 0) = x.1) ∧
      (∀ a : A, (Polynomial.C a).coeff 0 = a) ∧
      (∀ x y : standardGrading A 0,
        (x * y).1.coeff 0 = x.1.coeff 0 * y.1.coeff 0) ∧
      (∀ x y : standardGrading A 0,
        (x + y).1.coeff 0 = x.1.coeff 0 + y.1.coeff 0) := sorry

/-- The degree-zero piece of the standard polynomial grading is canonically `A`. -/
noncomputable def degreeZeroRingEquiv : standardGrading A 0 ≃+* A where
  toFun x := x.1.coeff 0
  invFun a := ⟨Polynomial.C a, (degreeZeroRingEquiv_laws A).1 a⟩
  left_inv x := Subtype.ext ((degreeZeroRingEquiv_laws A).2.1 x)
  right_inv a := (degreeZeroRingEquiv_laws A).2.2.1 a
  map_mul' x y := (degreeZeroRingEquiv_laws A).2.2.2.1 x y
  map_add' x y := (degreeZeroRingEquiv_laws A).2.2.2.2 x y

/-- The degree-zero ring equivalence induces an isomorphism of affine schemes. -/
noncomputable def degreeZeroSpecIso :
    Spec (.of (standardGrading A 0)) ≅ Spec (.of A) :=
  (Scheme.Spec.mapIso (degreeZeroRingEquiv A).toCommRingCatIso.op).symm

/-- The canonical structure morphism from the standard polynomial Proj to `Spec A`. -/
noncomputable def toSpec : Proj (standardGrading A) ⟶ Spec (.of A) :=
  Proj.toSpecZero (standardGrading A) ≫ (degreeZeroSpecIso A).hom

/-- The canonical structure morphism from standard polynomial Proj to `Spec A` is an isomorphism. -/
instance toSpec_isIso : IsIso (toSpec A) := sorry

/-- The underlying map of the canonical morphism from the standard polynomial
Proj to `Spec A` is a homeomorphism. -/
theorem toSpec_isHomeomorph : IsHomeomorph (toSpec A).base := sorry

/-- The underlying map of the canonical morphism from the standard polynomial
Proj to `Spec A` is bijective. -/
theorem toSpec_bijective : Function.Bijective (toSpec A).base := sorry

end AlgebraicGeometry.PolynomialProj
