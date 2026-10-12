/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import ReasLib.Algebra.Module.Graded.Shift.NatInt
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Associated
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic

/-!
# Weighted projective space of type (1, 2)

This file constructs the weighted polynomial ring `k[x, y]` with weights `1` and `2`, its
integral-scalar grading, the canonical twists on its projective spectrum, and the natural
multiplication morphisms `𝒪(n) ⊗ 𝒪(m) ⟶ 𝒪(n + m)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory MvPolynomial
open AlgebraicGeometry.Proj.AssociatedModule
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Proj.Weights12

variable (k : Type u) [Field k]

/-- The weighted polynomial ring `k[x, y]`, with variables indexed by `Fin 2`. -/
abbrev PolynomialRing :=
  MvPolynomial (Fin 2) k

/-- The weight function assigning degrees `1` and `2` to `x` and `y`. -/
def weight (i : Fin 2) : ℕ :=
  i.val + 1

/-- The weight of a variable is one more than its `Fin 2` index. -/
theorem weight_apply (i : Fin 2) : weight i = i.val + 1 := sorry

/-- The weighted homogeneous grading on `k[x, y]`, regarded as an integral submodule family. -/
abbrev grading : ℕ → Submodule ℤ (PolynomialRing k) :=
  fun n ↦ (weightedHomogeneousSubmodule k weight n).restrictScalars ℤ

/-- Membership in `grading k n` is weighted homogeneity of degree `n`. -/
theorem mem_grading_iff (n : ℕ) (f : PolynomialRing k) :
    f ∈ grading k n ↔ IsWeightedHomogeneous weight f n := sorry

/-- The canonical graded-algebra structure on the restricted weighted polynomial grading. -/
noncomputable instance instGradedAlgebra : GradedAlgebra (grading k) :=
  { (weightedGradedAlgebra k weight) with }

/-- The projective spectrum of the weighted polynomial ring of type `(1, 2)`. -/
abbrev ProjectiveScheme :=
  Proj (grading k)

/-- The integer-indexed regular grading of the weighted polynomial ring. -/
abbrev integerGrading : ℤ → Submodule ℤ (PolynomialRing k) :=
  DirectSum.Decomposition.natToIntGrading (grading k)

/-- The shift of the regular grading, whose degree-`n` piece is original degree `n + d`. -/
abbrev shifted (d : ℤ) : ℤ → Submodule ℤ (PolynomialRing k) :=
  GradedModule.shiftGrading (integerGrading k) d

/-- The canonical integral twist on the weighted projective spectrum of type `(1, 2)`. -/
noncomputable abbrev twist (n : ℤ) : (ProjectiveScheme k).Modules :=
  twistingSheaf (grading k) n

/-- The named twist is the associated sheaf of the regular grading shifted by `n`. -/
theorem twist_def (n : ℤ) :
    twist k n = twistingSheaf (grading k) n := sorry

/-- Multiplication on the tensor product of two shifted regular gradings preserves total
degree, with the output shifted by the sum of the two indices. -/
theorem mul_mapsTo (n m i : ℤ) :
    Set.MapsTo
      (TensorProduct.lid (PolynomialRing k) (PolynomialRing k)).toLinearMap
      (GradedModule.TensorProduct.grading (PolynomialRing k) (shifted k n) (shifted k m) i)
      (shifted k (n + m) i) := sorry

/-- The canonical multiplication morphism `𝒪(n) ⊗ 𝒪(m) ⟶ 𝒪(n + m)`, obtained from the
associated-sheaf tensor comparison followed by ring multiplication. -/
noncomputable def twistMulHom (n m : ℤ) :
    (tensorObj (twist k n) (twist k m) : (ProjectiveScheme k).Modules) ⟶ twist k (n + m) :=
  Tensor.hom (grading k) (shifted k n) (shifted k m) ≫
    map (grading k)
      (GradedModule.TensorProduct.gradingFor (PolynomialRing k) (grading k)
        (shifted k n) (shifted k m))
      (shifted k (n + m))
      (TensorProduct.lid (PolynomialRing k) (PolynomialRing k)).toLinearMap
      (mul_mapsTo k n m)

/-- The natural multiplication `𝒪(1) ⊗ 𝒪(1) ⟶ 𝒪(2)` on the weighted projective spectrum. -/
noncomputable abbrev mulOneOne :
    (tensorObj (twist k 1) (twist k 1) : (ProjectiveScheme k).Modules) ⟶ twist k 2 :=
  twistMulHom k 1 1

/-- The degree-one multiplication morphism is the canonical multiplication at indices `1` and
`1`. -/
theorem mulOneOne_def :
    mulOneOne k = twistMulHom k 1 1 := sorry

/-- The degree-one twist on the weighted binary projective spectrum is invertible. -/
noncomputable instance instInvertible_twistOne :
    Scheme.Modules.Invertible (twist k 1) := sorry

end AlgebraicGeometry.Proj.Weights12
