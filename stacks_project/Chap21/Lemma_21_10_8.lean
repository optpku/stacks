/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.Cofinal.Surjectivity
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

/- Lemma 21.10.8 (03F8): cofinal vanishing of first Cech cohomology makes the right map of a
short exact sequence of abelian sheaves surjective on sections.  The reusable owner is the
degree-parametric cofinal-vanishing predicate specialized to degree one. -/

#check @CategoryTheory.Cech.VanishesCofinally
#check @CategoryTheory.Cech.VanishesCofinally.exists_refinement
#check @CategoryTheory.Sheaf.Cech.VanishesCofinally

@[stacks 03F8 "surjectivity on sections from cofinal Cech vanishing"]
#check @CategoryTheory.Sheaf.Cech.VanishesCofinally.surjective_right
