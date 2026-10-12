/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AffineStratification
import StacksCheckRecall

universe u v

/- Lemma 37.73.2: a finite affine stratification whose index poset has strict-chain length
`n` yields an affine stratification indexed by `Fin (n + 1)`. -/
@[stacks 0F2T]
#check (AlgebraicGeometry.Scheme.FiniteAffineStratification.hasFinIndex_of_krullDim_eq :
  ∀ {X : AlgebraicGeometry.Scheme.{u}}
    (S : AlgebraicGeometry.Scheme.FiniteAffineStratification.{u, v} X) {n : ℕ},
      AlgebraicGeometry.Scheme.FiniteAffineStratification.indexDimension S =
        (n : WithBot ℕ∞) →
      AlgebraicGeometry.Scheme.FiniteAffineStratification.HasFinIndex X n)
