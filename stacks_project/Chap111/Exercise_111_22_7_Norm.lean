/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap111.Exercise_111_22_6_Determinant
public import stacks_project.Chap49.Lemma_49_4_3_ProjectiveTrace
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Finite-projective algebra norms

The algebra norm of a finite locally free (equivalently finite projective)
algebra is the projective determinant of left multiplication, parallel to
`Algebra.finiteProjectiveTrace`.
-/

@[expose] public section

noncomputable section

universe u v w

open scoped TensorProduct

namespace Module

variable {R : Type u} {S : Type v} {M : Type w}
  [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- Scalar extension of a projective module remains projective. -/
instance Projective.baseChange [Projective R M] :
    Projective S (TensorProduct R S M) := sorry

end Module

namespace Algebra

variable (A : Type u) {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]

/-- The algebra norm of a finite-projective algebra, defined without choosing a
global basis. -/
def finiteProjectiveNorm : B → A :=
  fun b => LinearMap.projectiveDet (lmul A B b)

/-- The finite-projective algebra norm is the projective determinant of left
multiplication. -/
theorem finiteProjectiveNorm_apply (b : B) :
    finiteProjectiveNorm A b = LinearMap.projectiveDet (lmul A B b) := sorry

/-- For a finite free algebra, the finite-projective norm agrees with `Algebra.norm`. -/
theorem finiteProjectiveNorm_eq_norm [Module.Free A B] (b : B) :
    finiteProjectiveNorm A b = norm A b := sorry

/-- The finite-projective algebra norm sends `1` to `1`. -/
theorem finiteProjectiveNorm_one :
    finiteProjectiveNorm A (1 : B) = 1 := sorry

/-- The finite-projective algebra norm is multiplicative. -/
theorem finiteProjectiveNorm_mul (b c : B) :
    finiteProjectiveNorm A (b * c) =
      finiteProjectiveNorm A b * finiteProjectiveNorm A c := sorry

/-- The finite-projective algebra norm commutes with extension of scalars. -/
theorem finiteProjectiveNorm_baseChange {A' : Type w} [CommRing A'] [Algebra A A']
    (b : B) :
    algebraMap A A' (finiteProjectiveNorm A b) =
      finiteProjectiveNorm A' ((1 : A') ⊗ₜ[A] b) := sorry

/-- On a finite product algebra `Fin n → A`, the finite-projective norm is the
product of the coordinates. -/
theorem finiteProjectiveNorm_pi {n : ℕ} (a : Fin n → A) :
    finiteProjectiveNorm A a = ∏ i, a i := sorry

end Algebra
