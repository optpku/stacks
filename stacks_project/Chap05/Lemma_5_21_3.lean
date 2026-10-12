/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.NowhereDense.Subspace
import StacksCheckRecall

@[expose] public section

open Set

universe u

variable {X : Type u} [TopologicalSpace X]

/- Lemma 5.21.3: a subset nowhere dense in an open subspace is nowhere dense
in the ambient space.  The ReasLib core does not need openness of that subtype. -/
@[stacks 03J0]
#check fun {U T : Set X} (hT : IsNowhereDense (Subtype.val ⁻¹' T : Set U))
    (_ : IsOpen U) (hTU : T ⊆ U) ↦ hT.of_subtypeVal hTU
