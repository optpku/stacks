/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Branch

@[expose] public section

open CategoryTheory

universe u

/- Lemma 33.40.2: Let `K/k` be a field extension, let `X` be a locally
algebraic `k`-scheme, and let `y` be a point of `X_K`. The geometric branch
number of `X_K` at `y` equals that of `X` at the canonical image of `y`. -/
@[stacks 0C40] #check
  (AlgebraicGeometry.FieldExtension.Over.geometricBranchNumberAt_eq :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      (X : Over (AlgebraicGeometry.Spec (CommRingCat.of k)))
      [AlgebraicGeometry.LocallyAlgebraic X]
      (y : (AlgebraicGeometry.FieldExtension.Over.baseChange k K X).left)
      (Ashx : Type u) [CommRing Ashx]
      [Algebra
        (X.left.presheaf.stalk
          (AlgebraicGeometry.FieldExtension.Over.toSource k K X y)) Ashx]
      [IsStrictHenselizationOf
        (X.left.presheaf.stalk
          (AlgebraicGeometry.FieldExtension.Over.toSource k K X y)) Ashx]
      (Ashy : Type u) [CommRing Ashy]
      [Algebra
        ((AlgebraicGeometry.FieldExtension.Over.baseChange k K X).left.presheaf.stalk y) Ashy]
      [IsStrictHenselizationOf
        ((AlgebraicGeometry.FieldExtension.Over.baseChange k K X).left.presheaf.stalk y) Ashy],
      X.left.geometricBranchNumberAt
          (AlgebraicGeometry.FieldExtension.Over.toSource k K X y) Ashx =
        (AlgebraicGeometry.FieldExtension.Over.baseChange k K X).left.geometricBranchNumberAt
          y Ashy)
