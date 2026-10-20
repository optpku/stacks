/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.QuotientSheaf.LocalSurjectivity

/-!
# Lemma 78.19.5

Equality in the fppf quotient sheaf of a pre-equivalence relation is witnessed
by relation arrows on an fppf covering, equivalently the comparison
`R ⟶ U ×_{U/R} U` is locally surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

/- Lemma 78.19.5 (1): equality of quotient-sheaf classes is witnessed by relation
points on an fppf covering. -/
@[stacks 046O] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.quotientClass_eq_iff_exists_cover :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
      (P : AlgebraicSpace.PreRelation U) (hP : P.IsPreEquivalence) {T : Over S}
      (a b : U.left.functorOfPoints.obj (op T)),
      P.quotientClass T a = P.quotientClass T b ↔
        ∃ cover : Precoverage.ZeroHypercover.{u + 1}
            (Scheme.fppfPrecoverage.comap (Over.forget S)) T,
          ∀ index : cover.I₀,
            ∃ relationPoint : P.left.left.functorOfPoints.obj (op (cover.X index)),
              U.left.functorOfPoints.map (cover.f index).op a =
                  P.s.left.app (op (cover.X index)) relationPoint ∧
                U.left.functorOfPoints.map (cover.f index).op b =
                  P.t.left.app (op (cover.X index)) relationPoint)

/- Lemma 78.19.5 (2): the comparison `R ⟶ U ×_{U/R} U` is locally surjective
as a morphism of fppf sheaves. -/
@[stacks 046O] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.relationToKernelPair_locallySurjective :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
      (P : AlgebraicSpace.PreRelation U) (hP : P.IsPreEquivalence),
      Sheaf.IsLocallySurjective P.relationToKernelPair)
