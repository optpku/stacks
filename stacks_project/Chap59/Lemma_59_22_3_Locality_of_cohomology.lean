/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cohomology.LocallyZero
import StacksCheckRecall

universe u v

open CategoryTheory

/-
Lemma 59.22.3 (Locality of cohomology)
-/

@[stacks 03P1] #check
  (@CategoryTheory.Sheaf.exists_cover_restrict_eq_zero_of_positive_cohomology_class :
    ∀ {C : Type u} [Category.{max u v} C] {J : GrothendieckTopology C}
      [HasSheafify J AddCommGrpCat.{max u v}]
      [HasExt.{max u v} (Sheaf J AddCommGrpCat.{max u v})]
      (F : Sheaf J AddCommGrpCat.{max u v}) {U : C} {n : ℕ},
      0 < n →
        (ξ : F.H' n U) →
          ∃ T : J.Cover U, ∀ I : T.Arrow,
            (((F.cohomologyPresheaf n).map I.f.op) ξ = 0))
