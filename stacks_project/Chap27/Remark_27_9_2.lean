module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import ReasLib.Algebra.Module.Graded.NatToInt
public import ReasLib.Algebra.Module.Graded.Shift
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.Tensor.Comparison
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Proj.AssociatedModule

noncomputable section

universe u

namespace AlgebraicGeometry.Proj.TensorCounterexample

variable (k : Type u) [Field k]

/-- The weighted polynomial ring `k[x, y, z]`, with variables indexed by `Fin 3`. -/
abbrev PolynomialRing :=
  MvPolynomial (Fin 3) k

/-- The weight function assigning degrees `1`, `2`, and `3` to `x`, `y`, and `z`. -/
def weight (i : Fin 3) : ℕ :=
  i.val + 1

/-- The weight of a variable is one more than its `Fin 3` index. -/
theorem weight_apply (i : Fin 3) : weight i = i.val + 1 := sorry

/-- The weighted homogeneous grading on `k[x, y, z]`. -/
abbrev grading : ℕ → Submodule k (PolynomialRing k) :=
  MvPolynomial.weightedHomogeneousSubmodule k weight

/-- Membership in `grading k n` is weighted homogeneity of degree `n`. -/
theorem mem_grading_iff (n : ℕ) (f : PolynomialRing k) :
    f ∈ grading k n ↔ MvPolynomial.IsWeightedHomogeneous weight f n := sorry

/-- The canonical graded-ring structure on the weighted polynomial grading. -/
noncomputable instance instGradedRingGrading : GradedRing (grading k) :=
  MvPolynomial.weightedGradedAlgebra k weight

/-- The natural weighted decomposition after restricting its homogeneous pieces to
`ℤ`-submodules. -/
noncomputable instance instDecompositionRestrictedGrading :
    DirectSum.Decomposition (fun n ↦ (grading k n).restrictScalars ℤ) where
  decompose' := (MvPolynomial.weightedDecomposition k weight).decompose'
  left_inv := sorry
  right_inv := sorry

/-- Scalar multiplication by a weighted polynomial respects the restricted natural grading. -/
instance instGradedSMulIntegerGrading :
    SetLike.GradedSMul (grading k) (fun n ↦ (grading k n).restrictScalars ℤ) := sorry

/-- The weighted grading extended by zero from natural to integer degrees. -/
abbrev integerGrading : ℤ → Submodule ℤ (PolynomialRing k) :=
  DirectSum.Decomposition.natToIntGrading
    (fun n ↦ (grading k n).restrictScalars ℤ)

/-- A natural component of `integerGrading` is the corresponding weighted component. -/
theorem integerGrading_nat (n : ℕ) :
    integerGrading k (n : ℤ) = (grading k n).restrictScalars ℤ := sorry

/-- The shift `S(d)`, whose degree-`n` piece is the original degree-`n + d` piece. -/
abbrev shifted (d : ℤ) : ℤ → Submodule ℤ (PolynomialRing k) :=
  GradedModule.shiftGrading (integerGrading k) d

/-- The degree-`n` piece of `shifted k d` is `integerGrading k (n + d)`. -/
theorem shifted_apply (d n : ℤ) :
    shifted k d n = integerGrading k (n + d) := sorry

/-- The canonical direct-sum decomposition of the shifted weighted grading. -/
noncomputable instance instDecompositionShifted (d : ℤ) :
    DirectSum.Decomposition (shifted k d) :=
  GradedModule.shiftDecomposition (integerGrading k) d

/-- Weighted multiplication respects every shifted grading. -/
instance instGradedSMulShifted (d : ℤ) :
    SetLike.GradedSMul (grading k) (shifted k d) := sorry

/-- The variable `z` is homogeneous of weighted degree `3`. -/
theorem z_mem_grading : MvPolynomial.X (2 : Fin 3) ∈ grading k 3 := sorry

/-- The degree-three homogeneous element represented by the variable `z`. -/
def z : grading k 3 :=
  ⟨MvPolynomial.X (2 : Fin 3), z_mem_grading k⟩

/-- The underlying polynomial of `z k` is the third variable. -/
theorem coe_z : (z k : PolynomialRing k) = MvPolynomial.X (2 : Fin 3) := sorry

/-- The left-unit tensor equivalence identifies the total grading of `S(1) ⊗[S] S(2)`
degreewise with the grading of `S(3)`. -/
theorem grading_map_lid (n : ℤ) :
    (GradedModule.TensorProduct.grading (PolynomialRing k)
      (shifted k 1) (shifted k 2) n).map
        ((TensorProduct.lid (PolynomialRing k) (PolynomialRing k)).toLinearMap.restrictScalars ℤ) =
      shifted k 3 n := sorry

/-- Remark 27.9.2 (1): for `k[x, y, z]` with weights `1`, `2`, and `3`, the localized
tensor comparison for `S(1)` and `S(2)` on the standard open determined by `z` is not an
isomorphism. -/
@[stacks 01ML]
theorem awayMap_not_isIso :
    ¬ IsIso (Tensor.awayHom
      (grading k) (shifted k 1) (shifted k 2) (z k)) := sorry

/-- Remark 27.9.2 (2): for `k[x, y, z]` with weights `1`, `2`, and `3`, the canonical
associated-sheaf tensor map from Lemma 27.9.1 for `S(1)` and `S(2)` is not an isomorphism. -/
@[stacks 01ML]
theorem associatedMap_not_isIso :
    ¬ IsIso (Tensor.hom
      (grading k) (shifted k 1) (shifted k 2)) := sorry

end AlgebraicGeometry.Proj.TensorCounterexample
