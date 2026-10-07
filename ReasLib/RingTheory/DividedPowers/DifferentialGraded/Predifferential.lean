module

public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.ChainAlgebra
public import ReasLib.RingTheory.DividedPowers.GradedAlgebra.Predifferential
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.NonnegativeModel

/-!
# Chain divided-power algebras as divided-power predifferential algebras

A nonnegative chain divided-power algebra has an underlying divided-power graded algebra.  Its
differential restricts to the nonnegative pieces and extends by zero to the integer grading.  This
file packages that construction at the predifferential layer, where square-zero is a separate
property rather than part of the data.
-/

@[expose] public section

noncomputable section

universe u v

open ChainGradedAlgebra

namespace DividedPowerChainAlgebra

variable {R : Type u} [CommRing R]

/-- The differential from a positive natural piece, transported to the integer degree used by
homogeneous maps. -/
def positiveGradedDifferential (A : DividedPowerChainAlgebra.{u, v} R) (n : ℕ+) :
    A.toGradedAlgebra.toGradedAlgebra.piece n →ₗ[R]
      A.toGradedAlgebra.toChainGradedAlgebra.X (((n : ℕ) : ℤ) + (-1)) :=
  A.toChainDGAlgebra.modelPositiveDifferential n

/-- The degree-`-1` homogeneous map on the extension-by-zero grading induced by the chain
differential. -/
@[stacks 09PS "chain differential on the extension-by-zero grading"]
def gradedPredifferentialMap (A : DividedPowerChainAlgebra.{u, v} R) :
    HomogeneousMap A.toGradedAlgebra.toChainGradedAlgebra (-1) :=
  A.toChainDGAlgebra.modelPredifferentialMap

/-- On a positive natural degree, the extension-by-zero map is the original nonnegative
differential. -/
@[simp]
theorem gradedPredifferentialMap_ofNat_succ (A : DividedPowerChainAlgebra.{u, v} R) (n : ℕ)
    (x : A.toGradedAlgebra.toGradedAlgebra.piece (n + 1)) :
    A.gradedPredifferentialMap (n + 1) x =
      A.positiveGradedDifferential ⟨n + 1, Nat.zero_lt_succ n⟩ x := sorry

/-- In degree zero, the extension-by-zero map lands in the zero negative piece. -/
@[simp]
theorem gradedPredifferentialMap_zero (A : DividedPowerChainAlgebra.{u, v} R)
    (x : A.toGradedAlgebra.toGradedAlgebra.piece 0) :
    A.gradedPredifferentialMap 0 x = 0 := sorry

/-- On a negative degree, the extension-by-zero map is the zero map between zero pieces. -/
@[simp]
theorem gradedPredifferentialMap_negSucc (A : DividedPowerChainAlgebra.{u, v} R) (n : ℕ)
    (x : PUnit) :
    A.gradedPredifferentialMap (.negSucc n) x = 0 := sorry

/-- The restricted differential satisfies the graded Leibniz rule on the extension-by-zero
grading. -/
theorem gradedPredifferentialMap_mem (A : DividedPowerChainAlgebra.{u, v} R) :
    A.gradedPredifferentialMap ∈
      derivationSubmodule A.toGradedAlgebra.toChainGradedAlgebra (-1) := sorry

/-- The chain differential as a predifferential on the underlying divided-power graded algebra. -/
def gradedPredifferential (A : DividedPowerChainAlgebra.{u, v} R) :
    Predifferential A.toGradedAlgebra.toChainGradedAlgebra :=
  A.toChainDGAlgebra.modelPredifferential

/-- The extension-by-zero predifferential preserves the given divided powers. -/
theorem gradedPredifferential_preservesDP (A : DividedPowerChainAlgebra.{u, v} R) :
    A.toGradedAlgebra.PreservesDP A.gradedPredifferential := sorry

/-- Forget square-zero while retaining the canonical divided-power-compatible predifferential. -/
@[stacks 09PS "chain algebra as a divided-power predifferential algebra"]
def toGradedPredifferential (A : DividedPowerChainAlgebra.{u, v} R) :
    A.toGradedAlgebra.Predifferential where
  toPredifferential := A.gradedPredifferential
  preservesDP := A.gradedPredifferential_preservesDP

/-- The underlying predifferential of `toGradedPredifferential` is the extension-by-zero chain
differential. -/
@[simp]
theorem toGradedPredifferential_toPredifferential (A : DividedPowerChainAlgebra.{u, v} R) :
    A.toGradedPredifferential.toPredifferential = A.gradedPredifferential := sorry

/-- The canonical graded predifferential coming from a chain algebra is square-zero. -/
theorem toGradedPredifferential_isSquareZero (A : DividedPowerChainAlgebra.{u, v} R) :
    A.toGradedPredifferential.IsSquareZero := sorry

end DividedPowerChainAlgebra
