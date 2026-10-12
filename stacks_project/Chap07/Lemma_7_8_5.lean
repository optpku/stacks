/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Family.Sheaf.Refinement

/-!
# Lemma 7.8.5

The reusable core is separatedness along `Presieve.FactorsThru`; fixed-target
family morphisms and refinements merely induce the required factorization.
This chapter file retains the labeled source-facing recall.
-/

@[expose] public section

/- Lemma 7.8.5 (0G1K): if a fixed-target family refines another and a
set-valued presheaf is separated for the refining family, it is separated for
the refined family. -/
@[stacks 0G1K] #check @CategoryTheory.SemiRepresentableFamily.Over.isSeparatedFor_of_refines

/- Companion recalls expose the canonical presieve core and the two
fixed-target-family factorization bridges. -/
#check @CategoryTheory.Presieve.IsSeparatedFor.of_factorsThru
#check @CategoryTheory.SemiRepresentableFamily.Over.Hom.factorsThru
#check @CategoryTheory.SemiRepresentableFamily.Over.Refines.factorsThru
