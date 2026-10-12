/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sheaves.Sheaf
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.QuasiCompact
public import ReasLib.Topology.Opens.QuasiCompact
import StacksCheckRecall

/-!
# Sections of module sheaves over compact opens

This file records how the site-theoretic quasi-compact evaluation API specializes to open
subsets of a topological space.  The generic site declarations remain the sole theorem owners.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe w u

namespace SheafOfModules.Evaluation

/- Lemma 17.3.5 (01AI): specialize the reusable site-level owners below at the
canonical site of opens.  The topology bridge turns `IsCompact U` into the
`QuasiCompactObject` hypothesis required by those owners. -/

@[stacks 01AI "compact-open evaluation specialization"] #check SheafOfModules.Evaluation.sigmaComparison_isIso_of_quasiCompact

@[stacks 01AI "compact-open sigma comparison"] #check SheafOfModules.Evaluation.sigmaComparison_isIso_of_quasiCompact

@[stacks 01AI "compact-open quasi-compact bridge"] #check TopologicalSpace.Opens.quasiCompactObject_of_isCompact

end SheafOfModules.Evaluation
