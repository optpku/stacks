module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.Ring.Under.Basic
public import Mathlib.Algebra.Polynomial.Laurent
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Linearity
public import ReasLib.RingTheory.GradedAlgebra.DegreeZero

/-!
# Weight decompositions for module-valued functors

This module defines the Laurent maps and weight submodules associated to a nonnegatively graded
algebra, together with their behavior for module-valued functors satisfying flat base change.
-/

@[expose] public section

open CategoryTheory RingHom

noncomputable section

universe u

namespace GradedAlgebra

/-- The constant-coefficient inclusion `B →ₐ[A] LaurentPolynomial B`. -/
def laurentProjection (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    B →ₐ[A] LaurentPolynomial B where
  toRingHom := LaurentPolynomial.C
  commutes' := sorry

/-- The Laurent projection sends `b` to the constant Laurent polynomial `C b`. -/
theorem laurentProjection_apply (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (b : B) : laurentProjection A B b = LaurentPolynomial.C b := sorry

/-- The constant-coefficient Laurent projection is flat. -/
theorem laurentProjection_flat (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Flat (laurentProjection A B).toRingHom := sorry

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]

/-- The Laurent coaction of a nonnegatively graded algebra sends a homogeneous element of
degree `n` to `C b * T n`. -/
def laurentCoaction : B →ₐ[A] LaurentPolynomial B :=
  { (DirectSum.toSemiring
      (fun n ↦
        { toFun := fun b : 𝒜 n ↦
            LaurentPolynomial.C (b : B) * LaurentPolynomial.T (n : ℤ)
          map_zero' := sorry
          map_add' := sorry })
      sorry sorry).comp (DirectSum.decomposeRingEquiv 𝒜).toRingHom with
    commutes' := sorry }

/-- The Laurent coaction has the expected value on a homogeneous element. -/
theorem laurentCoaction_apply_of_mem (n : ℕ) (b : B) (hb : b ∈ 𝒜 n) :
    laurentCoaction 𝒜 b =
      LaurentPolynomial.C b * LaurentPolynomial.T (n : ℤ) := sorry

/-- The endomorphism `B →ₐ[A] B` obtained by projecting to degree zero and then including
the degree-zero subalgebra into `B`. -/
def degreeZeroEnd : B →ₐ[A] B :=
  (IsScalarTower.toAlgHom A (𝒜 0) B).comp (projZeroAlgHom 𝒜)

/-- The degree-zero endomorphism evaluates by the canonical graded-ring projection. -/
theorem degreeZeroEnd_apply (b : B) :
    degreeZeroEnd 𝒜 b = GradedRing.projZeroRingHom 𝒜 b := sorry

end GradedAlgebra

namespace ModuleValuedFunctor

variable {A : CommRingCat.{u}} {B : Type u} [CommRing B] [Algebra A B]
variable (F : ModuleValuedFunctor.{u, u} A)

/-- The weight-`k` submodule consists of the elements on which the grading coaction agrees with
constant Laurent extension followed by multiplication by `T k`. -/
def weightSubmodule (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ) :
    Submodule A ((ModuleCat.restrictScalars (algebraMap A B)).obj
      (F.obj (CommRingCat.mkUnder A B))) where
  carrier := { x |
    ((F.obj (CommRingCat.mkUnder A (LaurentPolynomial B))).smul
      (LaurentPolynomial.T k)).hom
        (F.map (GradedAlgebra.laurentProjection A B).toUnder x) =
      (F.map (GradedAlgebra.laurentCoaction 𝒜).toUnder x :
        F.obj (CommRingCat.mkUnder A (LaurentPolynomial B))) }
  zero_mem' := sorry
  add_mem' := sorry
  smul_mem' := sorry

/-- Membership in a weight submodule is equivalent to the Laurent weight equation. -/
theorem mem_weightSubmodule_iff (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ)
    (x : (ModuleCat.restrictScalars (algebraMap A B)).obj
      (F.obj (CommRingCat.mkUnder A B))) :
    x ∈ weightSubmodule F 𝒜 k ↔
      ((F.obj (CommRingCat.mkUnder A (LaurentPolynomial B))).smul
        (LaurentPolynomial.T k)).hom
          (F.map (GradedAlgebra.laurentProjection A B).toUnder x) =
        (F.map (GradedAlgebra.laurentCoaction 𝒜).toUnder x :
          F.obj (CommRingCat.mkUnder A (LaurentPolynomial B))) := sorry

/-- Flat base change makes the integer-indexed weight submodules an internal direct sum. -/
theorem weightSubmodule_isInternal (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    (h_flat : F.HasFlatBaseChange) :
    DirectSum.IsInternal (F.weightSubmodule 𝒜) := sorry

/-- The functorial endomorphism induced by projection through degree zero has image in the
weight-zero submodule. -/
theorem degreeZero_image_le_weightZero (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    (h_flat : F.HasFlatBaseChange) :
    ∀ x : F.obj (CommRingCat.mkUnder A B),
      F.map (GradedAlgebra.degreeZeroEnd 𝒜).toUnder x ∈ F.weightSubmodule 𝒜 0 := sorry

end ModuleValuedFunctor
