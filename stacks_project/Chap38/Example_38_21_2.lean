/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Flattening.Counterexample
import StacksCheckRecall

universe u

/- Example 38.21.2 (1): every infinitesimal fiber over
`Spec(k[x, y] / (x, y) ^ n)` is a singleton. -/
@[stacks 0FJ1]
#check
  (AlgebraicGeometry.Scheme.Flattening.Counterexample.infinitesimalFiberIsSingleton :
    ∀ (k : Type u) [Field k] (n : ℕ),
      Nonempty
          ((AlgebraicGeometry.Scheme.Flattening.Counterexample.functor k).obj
            (Opposite.op (AlgebraicGeometry.Scheme.OverSpec.affine
              (CategoryTheory.CommRingCat.IdealPower.projection
                (AlgebraicGeometry.PuncturedAffineSpace.originIdeal (Fin 2) k) n)))) ∧
        ∀ x y : (AlgebraicGeometry.Scheme.Flattening.Counterexample.functor k).obj
          (Opposite.op (AlgebraicGeometry.Scheme.OverSpec.affine
            (CategoryTheory.CommRingCat.IdealPower.projection
              (AlgebraicGeometry.PuncturedAffineSpace.originIdeal (Fin 2) k) n))),
          x = y)

/- Example 38.21.2 (2): the fiber over `Spec(k[[x, y]])` is empty. -/
@[stacks 0FJ1]
#check
  (AlgebraicGeometry.Scheme.Flattening.Counterexample.completionFiberIsEmpty :
    ∀ (k : Type u) [Field k],
      ¬ Nonempty
        ((AlgebraicGeometry.Scheme.Flattening.Counterexample.functor k).obj
          (Opposite.op (AlgebraicGeometry.Scheme.OverSpec.affine
            (CommRingCat.ofHom MvPolynomial.coeToMvPowerSeries.ringHom)))))

/- Example 38.21.2 (3): the flattening functor is not represented by an algebraic space over
`Spec(k[x, y])`. -/
@[stacks 0FJ1]
#check
  (AlgebraicGeometry.Scheme.Flattening.Counterexample.notRepresentableByAlgebraicSpace :
    ∀ (k : Type u) [Field k],
      ¬ ∃ X : AlgebraicGeometry.AlgebraicSpace
          (AlgebraicGeometry.Spec
            (CommRingCat.of (MvPolynomial (Fin 2) k))),
        Nonempty
          (X.functorOfPoints ≅
            AlgebraicGeometry.Scheme.Flattening.Counterexample.functor k))

/- Example 38.21.2 (4): the universal flattening over `Spec(k[x, y])` does not exist. -/
@[stacks 0FJ1]
#check
  (AlgebraicGeometry.Scheme.Flattening.Counterexample.noUniversalFlattening :
    ∀ (k : Type u) [Field k],
      ¬ (AlgebraicGeometry.Scheme.Flattening.Counterexample.functor k).IsRepresentable)
