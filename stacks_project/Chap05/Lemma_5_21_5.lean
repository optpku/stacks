/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.Maps.Basic
import StacksCheckRecall

@[expose] public section

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : X → Y} {T : Set X}

/- Lemma 5.21.5: the image of a nowhere dense subset under a homeomorphism
onto a closed subset is nowhere dense.  Continuity is already part of the
closed-embedding owner. -/
@[stacks 03HQ]
#check fun (hf : Topology.IsClosedEmbedding f) (_ : Continuous f)
    (hT : IsNowhereDense T) ↦ hf.isInducing.isNowhereDense_image hT
