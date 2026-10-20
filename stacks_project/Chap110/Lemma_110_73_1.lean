/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.NonEffectiveness
import StacksCheckRecall

/-!
# An algebraic stack not satisfying strong formal effectiveness

The classifying stack of an abelian variety over an algebraically closed field
that is not an algebraic closure of a finite field admits a sequential inverse
system of objects which is not effective in the sense of Remark 98.20.2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver.StrongEffectiveness
open scoped CategoryTheory.MonObj

noncomputable section

universe u

/- Lemma 110.73.1: if `k` is algebraically closed and not an algebraic closure of a
finite field, and `A` is a nonzero abelian variety over `k` (`¬ IsIso A.hom`), then
the classifying stack `AlgebraicStack.classifying (Grp.mk A)` admits a formal object
system that is not effective in the sense of Remark 98.20.2. -/
@[stacks 0CXX] #check
  (AlgebraicGeometry.GroupoidsOver.StrongEffectiveness.exists_not_isEffective :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (hk : ¬ IsAlgebraicClosureOfFiniteField k)
      (A : SchemeOverField k) [GrpObj A] [AbelianVariety A] (hA : ¬ IsIso A.hom),
      ∃ ξ : FormalObjectSystem (AlgebraicStack.classifying (Grp.mk A)).p,
        ¬ ξ.IsEffective)

/- There is a non-effective system on `AlgebraicStack.classifying (Grp.mk A)` whose
ring system is the triangle system `k[x, y] / I^{n+1}` with coefficient ring `k`. -/
#check
  (AlgebraicGeometry.GroupoidsOver.StrongEffectiveness.exists_not_isEffective_of_triangle :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (hk : ¬ IsAlgebraicClosureOfFiniteField k)
      (A : SchemeOverField k) [GrpObj A] [AbelianVariety A] (hA : ¬ IsIso A.hom),
      ∃ ξ : FormalObjectSystem (AlgebraicStack.classifying (Grp.mk A)).p,
        ξ.ringSystem = CommRingCat.IdealPower.Positive.system (MvPolynomial.Triangle.ideal k) ∧
          ξ.coeffRing = CommRingCat.of k ∧ ¬ ξ.IsEffective)
