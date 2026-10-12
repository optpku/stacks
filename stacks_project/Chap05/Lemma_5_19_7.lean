/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Maps.Specialization
import StacksCheckRecall

@[expose] public section

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/- Lemma 5.19.7 (1): closed maps lift specializations; the source continuity
assumption is unnecessary for Mathlib's owner. -/
@[stacks 0066 "closed maps lift specializations"]
#check fun {f : X → Y} (hclosed : IsClosedMap f) (_ : Continuous f) ↦
  hclosed.specializingMap

/- Lemma 5.19.7 (2): an open continuous map from a Noetherian quasi-sober
space to a `T₀` space lifts generalizations. -/
@[stacks 0066 "open maps under Noetherian generic-point hypotheses lift generalizations"]
#check @IsOpenMap.generalizingMap_of_noetherianSpace_quasiSober_t0
