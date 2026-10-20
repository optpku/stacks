/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.Presentation.LengthTwo.Simplicial
import StacksCheckRecall

/-!
# An explicit polynomial construction through degree two

The presentation determines polynomial terms through degree two and an auxiliary
coskeleton. The checks below record the construction and its source assertions.
-/

@[expose] public section

universe u

variable {A B ι σ : Type u} [CommRing A] [CommRing B] [Algebra A B]

/- Example 92.5.9 (1). The explicit two-truncated polynomial diagram has terms
A[u_i], A[u_i, x_t], and A[u_i, y_t, z_t, v_r, w_{t,t'}], with the prescribed
faces and degeneracies. Its auxiliary two-coskeleton is checked separately. -/
@[stacks 09D4] #check (Algebra.Presentation.LengthTwo.truncatedTwo :
  (P : Algebra.Presentation A B ι σ) →
    CategoryTheory.SimplicialObject.Truncated (CategoryTheory.Over (CommAlgCat.of A B)) 2)

#check (Algebra.Presentation.LengthTwo.simplicial :
  (P : Algebra.Presentation A B ι σ) →
    CategoryTheory.SimplicialObject (CategoryTheory.Over (CommAlgCat.of A B)))

/- Example 92.5.9 (2). The sequence P1 → P0 → B → 0 given by d0 - d1
and the presentation map is exact. -/
@[stacks 09D4] #check (Algebra.Presentation.LengthTwo.exact_faceSub :
  (P : Algebra.Presentation A B ι σ) →
    Function.Exact
      (fun p : Algebra.Presentation.LengthTwo.term1 P ↦
        Algebra.Presentation.LengthTwo.faceZero P p - Algebra.Presentation.LengthTwo.faceOne P p)
      (fun p : P.Ring ↦ MvPolynomial.aeval P.val p) ∧
    Function.Surjective (fun p : P.Ring ↦ MvPolynomial.aeval P.val p))

/- Example 92.5.9 (3). The joint face map P1 → P0 ×_B P0 is surjective. -/
@[stacks 09D4] #check (Algebra.Presentation.LengthTwo.toPullback_surjective :
  (P : Algebra.Presentation A B ι σ) → {p0 p1 : P.Ring} →
    MvPolynomial.aeval P.val p0 = MvPolynomial.aeval P.val p1 →
    ∃ q : Algebra.Presentation.LengthTwo.term1 P,
      Algebra.Presentation.LengthTwo.faceZero P q = p0 ∧
      Algebra.Presentation.LengthTwo.faceOne P q = p1)

/- Example 92.5.9 (4). The augmentation of the one-coskeleton of the explicit
one-truncated object is a trivial Kan fibration. -/
@[stacks 09D4] #check (Algebra.Presentation.LengthTwo.coskOne_trivialKan :
  (P : Algebra.Presentation A B ι σ) →
    SSet.modelCategoryQuillen.I.rlp
      (Algebra.PolynomialSite.underlyingSSetMap
        (Algebra.Presentation.LengthTwo.coskOneAugmentation P)))

/- Example 92.5.9 (5). The polynomial map P2 → cosk1(P)_2 is surjective. -/
@[stacks 09D4] #check (Algebra.Presentation.LengthTwo.toMatching_surjective :
  (P : Algebra.Presentation A B ι σ) →
    {g0 g1 g2 : Algebra.Presentation.LengthTwo.term1 P} →
    Algebra.Presentation.LengthTwo.Triple.Compatible P g0 g1 g2 →
    ∃ q : Algebra.Presentation.LengthTwo.term2 P,
      Algebra.Presentation.LengthTwo.faceTwo P 0 q = g0 ∧
      Algebra.Presentation.LengthTwo.faceTwo P 1 q = g1 ∧
      Algebra.Presentation.LengthTwo.faceTwo P 2 q = g2)
