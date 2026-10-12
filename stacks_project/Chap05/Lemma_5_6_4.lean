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
variable {f : X → Y}

/- Lemma 5.6.4: the source's hypotheses are canonically represented by Mathlib's
`IsOpenQuotientMap`. -/
@[stacks 02YB "surjective continuous open maps"]
#check IsOpenQuotientMap

/- Lemma 5.6.4 (1): under a surjective continuous open map, preimage commutes with closure. -/
@[stacks 02YB "closure commutes with preimage"]
#check fun (hf : IsOpenQuotientMap f) (T : Set Y) ↦
  hf.preimage_closure_eq_closure_preimage (T := T)

/- Lemma 5.6.4 (2): under a surjective continuous open map, a subset is closed exactly when its
preimage is closed. -/
@[stacks 02YB "closed subsets are reflected by preimage"]
#check fun (hf : IsOpenQuotientMap f) (T : Set Y) ↦
  hf.isClosed_iff_preimage (T := T)

/- Lemma 5.6.4 (3): under a surjective continuous open map, a subset is open exactly when its
preimage is open. -/
@[stacks 02YB "open subsets are reflected by preimage"]
#check fun (hf : IsOpenQuotientMap f) (T : Set Y) ↦
  hf.isOpen_iff_preimage (T := T)

/- Lemma 5.6.4 (4): under an open quotient map, a subset is locally closed exactly when its
preimage is locally closed. -/
@[stacks 02YB "locally closed subsets are reflected by preimage"]
#check fun (hf : IsOpenQuotientMap f) (T : Set Y) ↦
  hf.isLocallyClosed_iff_preimage (T := T)

/- Lemma 5.6.4 (5): a surjective continuous open map is a quotient map. -/
@[stacks 02YB "surjective continuous open maps are quotient maps"]
#check fun (hf : IsOpenQuotientMap f) ↦ hf.isQuotientMap
