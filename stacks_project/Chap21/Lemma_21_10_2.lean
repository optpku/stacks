/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.Sheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

/- Lemma 21.10.2 (Tag 03AW): degree-zero Čech cohomology of an abelian sheaf is its sections,
and positive-degree Čech cohomology vanishes on injective coefficients.  The reusable owners are
the sheaf-level Čech functor and its degree-zero and acyclicity comparison statements. -/

@[stacks 03AW "Čech cohomology functor on abelian sheaves"]
#check @CategoryTheory.cechCohomologyOnSheaves

#check @CategoryTheory.cechCohomologyOnSheaves_obj_obj

@[stacks 03AW "degree-zero Čech cohomology of a sheaf"]
#check @CategoryTheory.cechCohomology_zero_of_sheaf

#check @CategoryTheory.cechCohomologyOnSheaves_zero_of_sheaf

@[stacks 03AW "positive Čech acyclicity of injective sheaves"]
#check @CategoryTheory.cechCohomology_isZero_of_injective_succ

#check @CategoryTheory.cechCohomologyOnSheaves_isZero_of_injective_succ
#check @CategoryTheory.cechCohomology_isZero_of_pos_of_injective
#check @CategoryTheory.cechCohomologyOnSheaves_isZero_of_pos_of_injective
