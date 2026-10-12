/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowMotive.Functor
public import ReasLib.AlgebraicGeometry.Correspondence.GradedCategory.Linear
public import ReasLib.CategoryTheory.Idempotents.Karoubi.Linear

@[expose] public section

open CategoryTheory

universe u

variable (k : Type u) [Field k]

/- Lemma 45.4.1: the category of Chow motives over `k` is `ℚ`-linear, and graph
correspondences define a contravariant functor sending `X` to `(X, 1, 0)` and `f` to
`[Γ_f]`. -/
@[stacks 0FGA] #check
  (ChowMotive.hFunctor k :
    (AlgebraicGeometry.Correspondence.Graded.SchemeCategory k)ᵒᵖ ⥤
      ChowMotive k (fun _ ↦ AlgebraicGeometry.Correspondence.GradedCategory k))
#check
  (inferInstance : Linear ℚ
    (ChowMotive k (fun _ ↦ AlgebraicGeometry.Correspondence.GradedCategory k)))
