/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.Chaotic
import StacksCheckRecall

@[expose] public section

/- The auxiliary entry is a compatibility recall for the canonical 0GYV owners.  The
definition itself and its membership API live in ReasLib; this file must not make the
shared layer depend on the chapter definition. -/

@[stacks 0GYV "canonical quasi-coherent derived modules"]
#check @CategoryTheory.ModulesOnCategory.Chaotic.isQuasiCoherent

@[stacks 0GYV "canonical quasi-coherent derived-module subcategory"]
#check @CategoryTheory.ModulesOnCategory.Chaotic.QC

@[stacks 0GYV "canonical quasi-coherence membership"]
#check @CategoryTheory.ModulesOnCategory.Chaotic.mem_iff

@[stacks 0GYV "canonical comparison isomorphism"]
#check @CategoryTheory.ModulesOnCategory.Chaotic.comparison_isIso
