/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
