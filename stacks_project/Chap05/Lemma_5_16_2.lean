/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Noetherian.Constructible
import StacksCheckRecall

@[expose] public section

universe u v

open Set TopologicalSpace Topology

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [NoetherianSpace X] [NoetherianSpace Y] {f : X → Y}

/- Lemma 5.16.2: for a continuous map of Noetherian spaces, the preimage of a
constructible subset is constructible.  The ReasLib owner only needs
Noetherianity of the source. -/
@[stacks 053Y]
#check fun {E : Set Y} (hE : IsConstructible E) (hf : Continuous f) ↦
  hE.preimage_of_continuous_of_noetherianSpace hf
