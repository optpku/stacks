/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Grassmannian.ProjectiveSpace
public import stacks_project.Chap27.Lemma_27_13_1
public import stacks_project.Chap27.Definition_27_22_2

@[expose] public section

/- Lemma 27.22.3: for `n > 0`, every explicit model of `G(n, n + 1)` is canonically
isomorphic to integral projective `n`-space relative to its projective-space representation. -/
@[stacks 089V] #check
  (AlgebraicGeometry.Grassmannian.Model.selfSuccIsoProjectiveSpace :
    ∀ (n : ℕ) (hn : 0 < n)
      (P : AlgebraicGeometry.Grassmannian.Model n (n + 1) hn (Nat.lt_succ_self n))
      (R : CategoryTheory.Functor.RepresentableBy
        (AlgebraicGeometry.ProjectiveSpaceDatumClass.functor n)
        (AlgebraicGeometry.ProjectiveSpace.scheme ℤ n)),
      P.scheme ≅ AlgebraicGeometry.ProjectiveSpace.scheme ℤ n)
