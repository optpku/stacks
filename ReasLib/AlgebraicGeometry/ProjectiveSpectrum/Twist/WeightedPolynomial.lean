/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import ReasLib.Algebra.Module.Graded.Shift.NatInt
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Associated
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic

/-!
# Twists on weighted polynomial projective spectra

The polynomial rings with weights `(1, 2, 3)` and `(1, 2)` carry canonical weighted gradings
and twisting sheaves on their projective spectra. Over a field, the former has a noninvertible
degree-one twist, while the latter has an invertible degree-one twist whose squared
multiplication to the degree-two twist is not an isomorphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory MvPolynomial
open AlgebraicGeometry.Proj.AssociatedModule
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Proj.Weights123

section Constructions

variable (k : Type u) [CommRing k]

/-- The polynomial ring `k[x, y, z]`, with variables indexed by `Fin 3`. -/
abbrev PolynomialRing :=
  MvPolynomial (Fin 3) k

/-- The weight function assigning degrees `1`, `2`, and `3` to `x`, `y`, and `z`. -/
def weight (i : Fin 3) : ℕ :=
  i.val + 1

/-- The weight of a variable is one more than its `Fin 3` index. -/
theorem weight_apply (i : Fin 3) : weight i = i.val + 1 := rfl

/-- The weighted homogeneous grading on `k[x, y, z]`, regarded as an integral submodule family. -/
abbrev grading : ℕ → Submodule ℤ (PolynomialRing k) :=
  fun n ↦ (weightedHomogeneousSubmodule k weight n).restrictScalars ℤ

/-- Membership in `grading k n` is weighted homogeneity of degree `n`. -/
theorem mem_grading_iff (n : ℕ) (f : PolynomialRing k) :
    f ∈ grading k n ↔ IsWeightedHomogeneous weight f n := Iff.rfl

/-- The canonical graded-algebra structure on the restricted weighted polynomial grading. -/
noncomputable instance instGradedAlgebra : GradedAlgebra (grading k) :=
  { (weightedGradedAlgebra k weight) with }

/-- The projective spectrum of the weighted polynomial ring of type `(1, 2, 3)`. -/
abbrev ProjectiveScheme :=
  Proj (grading k)

/-- The canonical integral twist on the weighted projective spectrum of type `(1, 2, 3)`. -/
noncomputable abbrev twist (n : ℤ) : (ProjectiveScheme k).Modules :=
  twistingSheaf (grading k) n

/-- The named twist is the associated sheaf of the regular grading shifted by `n`. -/
theorem twist_def (n : ℤ) :
    twist k n = twistingSheaf (grading k) n := rfl

end Constructions

/-- The degree-one twist on the weighted projective spectrum of `k[x, y, z]` with weights
`(1, 2, 3)` over a field is not invertible. -/
theorem twistOne_not_invertible (k : Type u) [Field k] :
    ¬ Scheme.Modules.Invertible (twist k 1) := sorry

end AlgebraicGeometry.Proj.Weights123

namespace AlgebraicGeometry.Proj.Weights12

section Constructions

variable (k : Type u) [CommRing k]

/-- The polynomial ring `k[x, y]`, with variables indexed by `Fin 2`. -/
abbrev PolynomialRing :=
  MvPolynomial (Fin 2) k

/-- The weight function assigning degrees `1` and `2` to `x` and `y`. -/
def weight (i : Fin 2) : ℕ :=
  i.val + 1

/-- The weight of a variable is one more than its `Fin 2` index. -/
theorem weight_apply (i : Fin 2) : weight i = i.val + 1 := rfl

/-- The weighted homogeneous grading on `k[x, y]`, regarded as an integral submodule family. -/
abbrev grading : ℕ → Submodule ℤ (PolynomialRing k) :=
  fun n ↦ (weightedHomogeneousSubmodule k weight n).restrictScalars ℤ

/-- Membership in `grading k n` is weighted homogeneity of degree `n`. -/
theorem mem_grading_iff (n : ℕ) (f : PolynomialRing k) :
    f ∈ grading k n ↔ IsWeightedHomogeneous weight f n := Iff.rfl

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
    twist k n = twistingSheaf (grading k) n := rfl

/-- The canonical multiplication morphism `𝒪(n) ⊗ 𝒪(m) ⟶ 𝒪(n + m)`, obtained from the
associated-module shift comparison and addition of grading shifts. -/
noncomputable def twistMulHom (n m : ℤ) :
    (tensorObj (twist k n) (twist k m) : (ProjectiveScheme k).Modules) ⟶ twist k (n + m) :=
  ShiftComparison.canonicalHom (grading k) (shifted k n) m ≫
    eqToHom (by
      change sheaf (grading k) (GradedModule.shiftGrading (shifted k n) m) =
        sheaf (grading k) (shifted k (n + m))
      simp only [shifted, GradedModule.shiftGrading_add])

/-- The natural multiplication `𝒪(1) ⊗ 𝒪(1) ⟶ 𝒪(2)` on the weighted projective spectrum. -/
noncomputable abbrev mulOneOne :
    (tensorObj (twist k 1) (twist k 1) : (ProjectiveScheme k).Modules) ⟶ twist k 2 :=
  twistMulHom k 1 1

/-- The degree-one multiplication morphism is the canonical multiplication at indices `1`
and `1`. -/
theorem mulOneOne_def :
    mulOneOne k = twistMulHom k 1 1 := rfl

end Constructions

/-- The degree-one twist on the weighted binary projective spectrum over a field is invertible. -/
noncomputable instance instInvertible_twistOne (k : Type u) [Field k] :
    Scheme.Modules.Invertible (twist k 1) := sorry

/-- Over a field, the degree-one twist on the weighted projective spectrum of `k[x, y]` with
weights `(1, 2)` is invertible, but its squared multiplication to the degree-two twist is not
an isomorphism. -/
theorem twistOne_invertible_mul_not_iso (k : Type u) [Field k] :
    Scheme.Modules.Invertible (twist k 1) ∧ ¬ IsIso (mulOneOne k) := by
  refine ⟨instInvertible_twistOne k, ?_⟩
  sorry

end AlgebraicGeometry.Proj.Weights12
