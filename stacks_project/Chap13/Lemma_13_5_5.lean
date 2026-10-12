/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Functor.HomologicalKernel.Triangulated
import StacksCheckRecall.CommandCrossRef

@[expose] public section

/- Lemma 13.5.5 (Stacks 05R5): maps detected as isomorphisms by all shifted
values of a homological functor form the canonical saturated denominator
system of its homological kernel. -/

#check @CategoryTheory.Functor.mem_homologicalKernel_trW_iff

@[stacks 05R5]
#check @CategoryTheory.Functor.HomologicalKernel.compatible

@[stacks 05R5]
#check @CategoryTheory.Functor.HomologicalKernel.saturated
