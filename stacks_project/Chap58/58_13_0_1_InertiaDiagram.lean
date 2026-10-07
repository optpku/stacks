module

public import ReasLib.Topology.Category.ProfiniteGrp.InertiaDiagram

@[expose] public section

universe u

open CategoryTheory

/- Compatibility bridge for the promoted profinite fundamental-group diagram API. -/
#check
  (EtaleFundamentalGroup.InertiaDiagram :
    ProfiniteGrp → ProfiniteGrp → ProfiniteGrp → ProfiniteGrp → ProfiniteGrp → Type)
