/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Unibranch

@[expose] public section

universe u

/- Lemma 33.40.3: Geometric unibranchness at a point is invariant under
extension of the ground field. -/
@[stacks 0C55] #check
  (AlgebraicGeometry.FieldExtension.Over.Unibranch.isGeometricallyUnibranchAt_iff :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k)))
      [AlgebraicGeometry.LocallyAlgebraic X]
      (y : (AlgebraicGeometry.FieldExtension.Over.baseChange k K X).left),
      X.left.isGeometricallyUnibranchAt
          (AlgebraicGeometry.FieldExtension.Over.toSource k K X y) ↔
        (AlgebraicGeometry.FieldExtension.Over.baseChange k K X).left.isGeometricallyUnibranchAt y)
