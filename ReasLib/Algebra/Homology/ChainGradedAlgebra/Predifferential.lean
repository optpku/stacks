/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.ChainGradedAlgebra.Derivation

/-!
# Predifferentials on chain-graded algebras

A predifferential is a degree-`-1` graded derivation without a square-zero
assumption.  Its square is constructed explicitly as a degree-`-2` derivation,
and square-zero and graded-closed conditions are exposed as separate predicates.
-/

@[expose] public section

universe u v

variable {R : Type u} [CommRing R]

namespace ChainGradedAlgebra

variable (A : ChainGradedAlgebra.{u, v} R)

/-- A predifferential on `A` is a graded derivation of degree `-1`. -/
@[stacks 09PR "infrastructure: predifferentials on chain-graded algebras"]
abbrev Predifferential := Derivation A (-1)

namespace Predifferential

variable {A : ChainGradedAlgebra.{u, v} R}

/-- The chain Leibniz rule for a predifferential on homogeneous elements. -/
theorem leibniz_apply (d : Predifferential A) (i j : ℤ)
    (a : A.X i) (b : A.X j) :
    d (i + j) (A.mul i j a b) =
      A.reindex (add_right_comm i (-1) j)
          (A.mul (i - 1) j (d i a) b) +
        i.negOnePow •
          A.reindex (add_assoc i j (-1)).symm
            (A.mul i (j - 1) a (d j b)) := sorry

/-- The homogeneous degree-`-2` map obtained by applying a predifferential twice. -/
def squareMap (d : Predifferential A) : HomogeneousMap A (-2) :=
  HomogeneousMap.comp (Derivation.toHomogeneousMap d) (Derivation.toHomogeneousMap d)

/-- The square map is the composite of the two degree-`-1` component maps. -/
@[simp]
theorem squareMap_apply (d : Predifferential A) (i : ℤ) (x : A.X i) :
    squareMap d i x =
      A.reindex (add_assoc i (-1) (-1)) (d (i - 1) (d i x)) := sorry

/-- The square of a predifferential satisfies the degree-`-2` graded Leibniz rule. -/
theorem squareMap_mem (d : Predifferential A) :
    squareMap d ∈ derivationSubmodule A (-2) := sorry

/-- The square of a predifferential, bundled as a degree-`-2` derivation. -/
@[stacks 09PR "infrastructure: the square derivation of a predifferential"]
def square (d : Predifferential A) : Derivation A (-2) :=
  ⟨squareMap d, squareMap_mem d⟩

/-- The homogeneous map underlying `square d` is `squareMap d`. -/
@[simp]
theorem square_toHomogeneousMap (d : Predifferential A) :
    Derivation.toHomogeneousMap (square d) = squareMap d := sorry

/-- Evaluation of the square derivation is evaluation of the square map. -/
@[simp]
theorem square_apply (d : Predifferential A) (i : ℤ) (x : A.X i) :
    square d i x = squareMap d i x := sorry

/-- A predifferential is square-zero when its explicit square map vanishes. -/
@[stacks 09PR "infrastructure: square-zero predifferentials"]
def IsSquareZero (d : Predifferential A) : Prop :=
  squareMap d = 0

/-- Square-zero can be checked by applying the predifferential twice to homogeneous elements. -/
theorem isSquareZero_iff (d : Predifferential A) :
    IsSquareZero d ↔ ∀ i : ℤ, ∀ x : A.X i, d (i - 1) (d i x) = 0 := sorry

/-- The square map vanishes exactly when the bundled square derivation vanishes. -/
theorem isSquareZero_iff_square_eq_zero (d : Predifferential A) :
    IsSquareZero d ↔ square d = 0 := sorry

end Predifferential

namespace Derivation

variable {A : ChainGradedAlgebra.{u, v} R} {k : ℤ}

/-- A degree-`k` derivation is closed under a predifferential when the two maps
graded-commute. -/
@[stacks 09PR "infrastructure: closed graded derivations"]
def IsClosed (D : Derivation A k) (d : Predifferential A) : Prop :=
  HomogeneousMap.GradedCommutes (toHomogeneousMap D) (toHomogeneousMap d)

/-- Closedness is the usual signed commutation equation with sign `(-1)^k`. -/
theorem isClosed_iff (D : Derivation A k) (d : Predifferential A) :
    IsClosed D d ↔
      HomogeneousMap.comp (toHomogeneousMap d) (toHomogeneousMap D) =
        k.negOnePow •
          HomogeneousMap.castDegree (add_comm (-1) k)
            (HomogeneousMap.comp (toHomogeneousMap D) (toHomogeneousMap d)) := sorry

/-- A degree-`-2` derivation is closed exactly when it commutes ordinarily
with the predifferential. -/
theorem isClosed_iff_commutes (D : Derivation A (-2)) (d : Predifferential A) :
    IsClosed D d ↔
      HomogeneousMap.Commutes (toHomogeneousMap D) (toHomogeneousMap d) := sorry

end Derivation

namespace Predifferential

variable {A : ChainGradedAlgebra.{u, v} R}

/-- The square derivation is closed under the original predifferential. -/
theorem square_isClosed (d : Predifferential A) :
    Derivation.IsClosed (square d) d := sorry

/-- The square derivation commutes ordinarily with the original predifferential. -/
theorem square_commutes (d : Predifferential A) :
    HomogeneousMap.Commutes (Derivation.toHomogeneousMap (square d))
      (Derivation.toHomogeneousMap d) := sorry

end Predifferential

end ChainGradedAlgebra
