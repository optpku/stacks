/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme.AffineRationalPoints
import StacksCheckRecall

/-!
# Schemes from affine covers of rational points after algebraic closure

A decent algebraic space locally of finite type over a field is a scheme if its
base change to the algebraic closure is a scheme whose finite sets of rational
points lie in affine opens.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CommRingCat

universe u

/- Lemma 72.10.7: A decent algebraic space locally of finite type over a field
is a scheme if its algebraic-closure base change is a scheme whose finite
families of rational points lie in affine opens. -/
@[stacks 0B88] #check
  (AlgebraicGeometry.AlgebraicSpace.IsScheme.of_finiteRationalPoints_affine :
    ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (CommRingCat.of k)))
      [IsDecent X] [LocallyOfFiniteType (SchemeRealization.toBase X)],
      IsScheme (AlgebraicSpace.baseChange (FieldExtension.specMap k (AlgebraicClosure k)) X) →
      finiteRationalPointsContainedInAffine
        (AlgebraicSpace.baseChange (FieldExtension.specMap k (AlgebraicClosure k)) X) →
      IsScheme X)
