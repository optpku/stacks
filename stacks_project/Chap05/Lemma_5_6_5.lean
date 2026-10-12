/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Maps.ClosedQuotient
import StacksCheckRecall

@[expose] public section

open Set Topology

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : X → Y}

/- Lemma 5.6.5: `IsClosedQuotientMap` packages the source's surjective, continuous, closed-map
setup without requiring downstream users to rebuild the implied quotient-map proof. -/
@[stacks 0AAU "surjective continuous closed maps"]
#check IsClosedQuotientMap

/- Lemma 5.6.5 (1): for a surjective closed continuous map, the closure of a subset of the
codomain is the image of the closure of its preimage. -/
@[stacks 0AAU "closure as the image of the closure of the preimage"]
#check fun (hf : IsClosedQuotientMap f) (T : Set Y) ↦
  hf.closure_eq_image_closure_preimage (T := T)

/- Lemma 5.6.5 (2): under a surjective continuous closed map, a subset is closed exactly when
its preimage is closed. -/
@[stacks 0AAU "closed subsets are reflected by preimage"]
#check fun (hf : IsClosedQuotientMap f) (T : Set Y) ↦
  hf.isClosed_iff_preimage (T := T)

/- Lemma 5.6.5 (3): under a surjective continuous closed map, a subset is open exactly when its
preimage is open. -/
@[stacks 0AAU "open subsets are reflected by preimage"]
#check fun (hf : IsClosedQuotientMap f) (T : Set Y) ↦
  hf.isOpen_iff_preimage (T := T)

/- Lemma 5.6.5 (4): under a closed quotient map, a subset is locally closed exactly when its
preimage is locally closed. -/
@[stacks 0AAU "locally closed subsets are reflected by preimage"]
#check fun (hf : IsClosedQuotientMap f) (T : Set Y) ↦
  hf.isLocallyClosed_iff_preimage (T := T)

/- Lemma 5.6.5 (5): a surjective continuous closed map is a quotient map. -/
@[stacks 0AAU "surjective continuous closed maps are quotient maps"]
#check fun (hf : IsClosedQuotientMap f) ↦ hf.isQuotientMap
