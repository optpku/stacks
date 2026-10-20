/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Category.ProfiniteGrp.InertiaDiagram
import StacksCheckRecall

@[expose] public section

/- 58.13.0.1: the fundamental-group diagram for the strict henselian, henselian, and ordinary
opens and their corresponding spectra. -/
@[stacks 0BSV] #check
  (EtaleFundamentalGroup.InertiaDiagram :
    ProfiniteGrp → ProfiniteGrp → ProfiniteGrp → ProfiniteGrp → ProfiniteGrp → Type)
