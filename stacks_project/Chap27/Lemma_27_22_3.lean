/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Grassmannian.ProjectiveSpace
public import stacks_project.Chap27.Lemma_27_13_1
public import stacks_project.Chap27.Definition_27_22_2

@[expose] public section

open CategoryTheory

/- Lemma 27.22.3: for `n > 0`, comparison uses the canonical datum
`(O(1), T_0, ..., T_n)`. The canonical isomorphism is uniquely characterized by
pullback of this datum to the universal rank-one quotient datum. -/
@[stacks 089V] #check
  (AlgebraicGeometry.Grassmannian.Model.existsUnique_selfSuccIsoProjectiveSpace :
    ∀ (n : ℕ) (hn : 0 < n)
      (P : AlgebraicGeometry.Grassmannian.Model n (n + 1) hn (Nat.lt_succ_self n)),
      ∃! e : P.scheme ≅ AlgebraicGeometry.ProjectiveSpace.scheme ℤ n,
        (AlgebraicGeometry.ProjectiveSpaceDatumClass.functor n).map e.hom.op
            (AlgebraicGeometry.ProjectiveSpaceDatumClass.universalClass n) =
          (AlgebraicGeometry.Grassmannian.selfSuccFunctorIso n).hom.app
            (Opposite.op P.scheme) P.point)

/- The data-returning variant requires explicit inverse bijections normalized at the
canonical coordinate datum; its value is independent of this representation input. -/
#check
  (AlgebraicGeometry.Grassmannian.Model.selfSuccIsoProjectiveSpace :
    ∀ (n : ℕ) (hn : 0 < n)
      (P : AlgebraicGeometry.Grassmannian.Model n (n + 1) hn (Nat.lt_succ_self n))
      (R : CategoryTheory.Functor.RepresentableBy
        (AlgebraicGeometry.ProjectiveSpaceDatumClass.functor n)
        (AlgebraicGeometry.ProjectiveSpace.scheme ℤ n))
      (_hR : R.homEquiv (𝟙 _) = AlgebraicGeometry.ProjectiveSpaceDatumClass.universalClass n),
      P.scheme ≅ AlgebraicGeometry.ProjectiveSpace.scheme ℤ n)

#check AlgebraicGeometry.Grassmannian.Model.selfSuccIsoProjectiveSpace_hom_classifies
#check AlgebraicGeometry.Grassmannian.Model.selfSuccIsoProjectiveSpace_eq
