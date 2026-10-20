module

public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.Scheme.OverField.CompleteLocalRing
public import ReasLib.RingTheory.PowerSeries.Multicross

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- A point is an `n`-branch multicross point when it is closed, `2 ≤ n`, and its
completed local ring is `k`-algebra equivalent to `Multicross.ring k n`. -/
def isMulticrossPoint {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) (x : X.left) (n : ℕ) : Prop :=
  x ∈ closedPoints X.left ∧ 2 ≤ n ∧
    Nonempty
      (AdicCompletion (IsLocalRing.maximalIdeal (stalkRing X x)) (stalkRing X x) ≃ₐ[k]
        Multicross.ring k n)

/-- The closedness, branch bound, and completed-local-ring characterization of an
`n`-branch multicross point. -/
theorem isMulticrossPoint_iff {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) (x : X.left) (n : ℕ) :
    isMulticrossPoint X x n ↔
      x ∈ closedPoints X.left ∧ 2 ≤ n ∧
        Nonempty
          (AdicCompletion (IsLocalRing.maximalIdeal (stalkRing X x)) (stalkRing X x) ≃ₐ[k]
            Multicross.ring k n) := sorry

/-- A multicross singularity is an `n`-branch multicross point for some `n`. -/
def isMulticrossSingularity {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) (x : X.left) : Prop :=
  ∃ n : ℕ, isMulticrossPoint X x n

/-- A multicross singularity is a closed point whose completed local ring is equivalent
to `Multicross.ring k n` for some `n ≥ 2`. -/
theorem isMulticrossSingularity_iff {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) (x : X.left) :
    isMulticrossSingularity X x ↔
      x ∈ closedPoints X.left ∧
        ∃ n : ℕ, 2 ≤ n ∧
          Nonempty
            (AdicCompletion (IsLocalRing.maximalIdeal (stalkRing X x)) (stalkRing X x) ≃ₐ[k]
              Multicross.ring k n) := sorry

/-- A multicross point with a specified branch count is a multicross singularity. -/
theorem isMulticrossPoint.isMulticrossSingularity {k : Type u} [Field k] [IsAlgClosed k]
    {X : SchemeOverField k} {x : X.left} {n : ℕ} (h : isMulticrossPoint X x n) :
    isMulticrossSingularity X x := sorry

end AlgebraicGeometry.SchemeOverField
