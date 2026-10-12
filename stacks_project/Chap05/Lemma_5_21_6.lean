/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Maps.OpenQuotient
import StacksCheckRecall

@[expose] public section

open Set Topology

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : X → Y} {T : Set Y}

/- Lemma 5.21.6 (1): under a continuous open map, the preimage of a closed nowhere dense set is
closed and nowhere dense. -/
@[stacks 03HR "preimages under continuous open maps"]
#check fun (hf : IsOpenMap f) (hcont : Continuous f)
    (hT : IsClosed T ∧ IsNowhereDense T) ↦
  hf.isClosed_isNowhereDense_preimage hcont hT

/- Lemma 5.21.6 (2): under a surjective continuous open map, a set is closed and nowhere dense
if and only if its preimage is closed and nowhere dense. -/
@[stacks 03HR "closed nowhere dense sets under surjective continuous open maps"]
#check fun (hf : IsOpenQuotientMap f) ↦
  hf.isClosed_isNowhereDense_iff_preimage (T := T)
