/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Category.ProfiniteGrp.InertiaDiagram

@[expose] public section

universe u

open CategoryTheory

/- Compatibility bridge for the promoted profinite fundamental-group diagram API. -/
#check
  (EtaleFundamentalGroup.InertiaDiagram :
    ProfiniteGrp → ProfiniteGrp → ProfiniteGrp → ProfiniteGrp → ProfiniteGrp → Type)
