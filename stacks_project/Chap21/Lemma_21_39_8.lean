/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.InverseImage
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/-! Lemma 21.39.8 (08QA) is the derived-colimit comparison for presheaf inverse image under the
existence of a cosimplicial object that is pointlike before and after whiskering, for both
abelian-group-valued and `B`-module-valued presheaves. The coefficient-general statement is owned
by `CategoryTheory.DerivedColimit`. -/

@[stacks 08QA "abelian inverse-image derived-colimit comparison"]
#check @CategoryTheory.DerivedColimit.inverseImage_isomorphic_of_exists_pointlike_abelian

@[stacks 08QA "module inverse-image derived-colimit comparison"]
#check @CategoryTheory.DerivedColimit.inverseImage_isomorphic_of_exists_pointlike_module
