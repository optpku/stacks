module

public import ReasLib.LinearAlgebra.Determinant.ProjectiveProperties
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Norms of finite-projective algebras

The algebra norm is the basis-independent determinant of left multiplication.
-/

@[expose] public section

noncomputable section

universe u v w

open scoped TensorProduct

namespace Algebra

variable (A : Type u) {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]

/-- The norm of a finite-projective algebra is the determinant of left multiplication. -/
def finiteProjectiveNorm : B → A :=
  fun b => LinearMap.projectiveDet (lmul A B b)

/-- The finite-projective norm evaluates to the projective determinant of left multiplication. -/
theorem finiteProjectiveNorm_apply (b : B) :
    finiteProjectiveNorm A b = LinearMap.projectiveDet (lmul A B b) := rfl

/-- On a finite free algebra, the finite-projective norm agrees with the usual algebra norm. -/
theorem finiteProjectiveNorm_eq_norm [Module.Free A B] (b : B) :
    finiteProjectiveNorm A b = norm A b := sorry

/-- The finite-projective algebra norm sends one to one. -/
theorem finiteProjectiveNorm_one :
    finiteProjectiveNorm A (1 : B) = 1 := sorry

/-- The finite-projective algebra norm is multiplicative. -/
theorem finiteProjectiveNorm_mul (b c : B) :
    finiteProjectiveNorm A (b * c) =
      finiteProjectiveNorm A b * finiteProjectiveNorm A c := sorry

/-- The finite-projective algebra norm as a multiplicative homomorphism. -/
def finiteProjectiveNormHom : B →* A where
  toFun := finiteProjectiveNorm A
  map_one' := finiteProjectiveNorm_one A
  map_mul' := finiteProjectiveNorm_mul A

/-- The finite-projective algebra norm commutes with arbitrary extension of scalars. -/
theorem finiteProjectiveNorm_baseChange {A' : Type w} [CommRing A'] [Algebra A A']
    (b : B) :
    algebraMap A A' (finiteProjectiveNorm A b) =
      finiteProjectiveNorm A' ((1 : A') ⊗ₜ[A] b) := sorry

/-- The norm on a finite product algebra is the product of its coordinates. -/
theorem finiteProjectiveNorm_pi {n : ℕ} (a : Fin n → A) :
    finiteProjectiveNorm A a = ∏ i, a i := sorry

end Algebra
