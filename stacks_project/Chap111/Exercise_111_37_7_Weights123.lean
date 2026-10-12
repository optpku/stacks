/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.BasicOpen

/-!
# Weighted projective space of type (1, 2, 3)

This file constructs the weighted polynomial ring `k[x, y, z]` with weights `1`, `2`, and `3`,
its integral-scalar grading, and the canonical twists on its projective spectrum.
-/

@[expose] public section

open AlgebraicGeometry MvPolynomial
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Proj.Weights123

variable (k : Type u) [Field k]

/-- The weighted polynomial ring `k[x, y, z]`, with variables indexed by `Fin 3`. -/
abbrev PolynomialRing :=
  MvPolynomial (Fin 3) k

/-- The weight function assigning degrees `1`, `2`, and `3` to `x`, `y`, and `z`. -/
def weight (i : Fin 3) : ℕ :=
  i.val + 1

/-- The weight of a variable is one more than its `Fin 3` index. -/
theorem weight_apply (i : Fin 3) : weight i = i.val + 1 := sorry

/-- The weighted homogeneous grading on `k[x, y, z]`, regarded as an integral submodule family. -/
abbrev grading : ℕ → Submodule ℤ (PolynomialRing k) :=
  fun n ↦ (weightedHomogeneousSubmodule k weight n).restrictScalars ℤ

/-- Membership in `grading k n` is weighted homogeneity of degree `n`. -/
theorem mem_grading_iff (n : ℕ) (f : PolynomialRing k) :
    f ∈ grading k n ↔ IsWeightedHomogeneous weight f n := sorry

/-- The canonical graded-algebra structure on the restricted weighted polynomial grading. -/
noncomputable instance instGradedAlgebra : GradedAlgebra (grading k) :=
  { (weightedGradedAlgebra k weight) with }

/-- The projective spectrum of the weighted polynomial ring of type `(1, 2, 3)`. -/
abbrev ProjectiveScheme :=
  Proj (grading k)

/-- The canonical integral twist on the weighted projective spectrum of type `(1, 2, 3)`. -/
noncomputable abbrev twist (n : ℤ) : (ProjectiveScheme k).Modules :=
  AssociatedModule.twistingSheaf (grading k) n

/-- The named twist is the associated sheaf of the regular grading shifted by `n`. -/
theorem twist_def (n : ℤ) :
    twist k n = AssociatedModule.twistingSheaf (grading k) n := sorry

end AlgebraicGeometry.Proj.Weights123
