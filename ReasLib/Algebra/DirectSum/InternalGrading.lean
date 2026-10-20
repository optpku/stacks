module

public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The internal grading of an external direct sum

An externally graded ring is itself internally graded by the ranges of its canonical summand
inclusions.  This file records the homogeneous subgroups, their explicit decomposition, and the
resulting `GradedRing` instance.
-/

@[expose] public section

open scoped DirectSum

noncomputable section

universe u v

namespace DirectSum.InternalGrading

variable {ι : Type u} [DecidableEq ι] [AddMonoid ι]
variable (A : ι → Type v) [∀ i, AddCommGroup (A i)] [DirectSum.GRing A]

/-- The internal degree-`i` subgroup of an external direct sum. -/
abbrev summand (i : ι) : AddSubgroup (⨁ i, A i) :=
  AddMonoidHom.range (DirectSum.of A i)

/-- The canonical inclusion of an external homogeneous piece into its internal summand. -/
def summandInclusion (i : ι) : A i →+ summand A i :=
  (DirectSum.of A i).codRestrict (summand A i) fun x ↦ ⟨x, rfl⟩

/-- The canonical summand inclusion is injective. -/
theorem summandInclusion_injective (i : ι) :
    Function.Injective (summandInclusion A i) := sorry

/-- Every element of an internal summand comes from its external homogeneous piece. -/
theorem summandInclusion_surjective (i : ι) :
    Function.Surjective (summandInclusion A i) := sorry

/-- An external homogeneous piece is additively equivalent to its internal summand. -/
def summandEquiv (i : ι) : A i ≃+ summand A i where
  toFun := summandInclusion A i
  invFun x := DirectSum.component ℤ ι A i x.1
  left_inv x := DirectSum.component.lof_self (R := ℤ) i x
  right_inv x := by
    obtain ⟨y, hy⟩ := x.2
    apply Subtype.ext
    change DirectSum.of A i (DirectSum.component ℤ ι A i x.1) = x.1
    rw [← hy]
    exact congrArg (DirectSum.of A i)
      (DirectSum.component.lof_self (R := ℤ) i y)
  map_add' x y := by
    apply Subtype.ext
    simp [summandInclusion]

/-- The forward summand equivalence is the canonical direct-sum inclusion. -/
@[simp]
theorem summandEquiv_apply (i : ι) (x : A i) :
    ((summandEquiv A i x : summand A i) : ⨁ i, A i) = DirectSum.of A i x := sorry

/-- The explicit decomposition of a direct sum into its internal homogeneous summands. -/
def decompose : (⨁ i, A i) →+ ⨁ i, summand A i :=
  (DirectSum.congrAddEquiv (summandEquiv A)).toAddMonoidHom

/-- Recomposition after the explicit homogeneous decomposition is the identity. -/
theorem decompose_left_inv (x : ⨁ i, A i) :
    DirectSum.coeAddMonoidHom (summand A) (decompose A x) = x := sorry

/-- Decomposition after canonical recomposition is the identity. -/
theorem decompose_right_inv (x : ⨁ i, summand A i) :
    decompose A (DirectSum.coeAddMonoidHom (summand A) x) = x := sorry

/-- The unit of the external direct-sum ring belongs to the degree-zero summand. -/
theorem one_mem_summand :
    (1 : ⨁ i, A i) ∈ summand A 0 := sorry

/-- Products of homogeneous elements belong to the summand of the sum of their degrees. -/
theorem mul_mem_summand {i j : ι} {x y : ⨁ i, A i}
    (hx : x ∈ summand A i) (hy : y ∈ summand A j) :
    x * y ∈ summand A (i + j) := sorry

/-- The internal summands contain the unit and are closed under multiplication. -/
instance instSetLikeGradedMonoid : SetLike.GradedMonoid (summand A) where
  one_mem := one_mem_summand A
  mul_mem := fun {i j} {x y} hx hy ↦
    mul_mem_summand A (i := i) (j := j) (x := x) (y := y) hx hy

/-- The explicit homogeneous decomposition supplies the canonical decomposition instance. -/
instance instDecomposition : DirectSum.Decomposition (summand A) where
  decompose' := decompose A
  left_inv := decompose_left_inv A
  right_inv := decompose_right_inv A

/-- The internal summands give an externally graded direct-sum ring its natural grading. -/
instance instGradedRing : GradedRing (summand A) where

end DirectSum.InternalGrading
