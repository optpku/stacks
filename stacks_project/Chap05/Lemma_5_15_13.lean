/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Constructible.LocallyClosed
import StacksCheckRecall

@[expose] public section

universe u

open Set TopologicalSpace Topology

variable {X : Type u} [TopologicalSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X]
  [CompactSpace X] {T : Set X}

/- Lemma 5.15.13: in a quasi-compact prespectral quasi-separated space, a
compact locally closed subset with retrocompact complement is constructible. The
ambient `CompactSpace` assumption records the source's quasi-compactness; the
canonical criterion itself is valid under the displayed weaker hypotheses. -/
@[stacks 0F2K]
#check fun (hT_loc : IsLocallyClosed T) (hT_compact : IsCompact T)
    (hTc_retro : IsRetrocompact Tᶜ) ↦
  hT_loc.isConstructible_of_isCompact_of_retrocompact_compl hT_compact hTc_retro
