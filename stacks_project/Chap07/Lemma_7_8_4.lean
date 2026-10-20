/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Family.Sheaf.Refinement

/-!
# Lemma 7.8.4

The reusable statement is owned by the fixed-target family API: tautological
equivalence identifies the generated sieves, and the sheaf condition is
invariant under that identification. This chapter file retains the labeled
source-facing recall.
-/

@[expose] public section

/- Lemma 7.8.4 (00VW): tautologically equivalent indexed families of morphisms
with the same target impose equivalent sheaf conditions on every presheaf. -/
@[stacks 00VW] #check @CategoryTheory.SemiRepresentableFamily.Over.TautologicallyEquivalent.isSheafFor_iff

/- Companion recall: the underlying canonical statement is that a presieve
sheaf condition depends only on its generated sieve. -/
#check @CategoryTheory.SemiRepresentableFamily.Over.TautologicallyEquivalent.ofArrows
#check @CategoryTheory.Presieve.isSheafFor_iff_of_generate_eq
