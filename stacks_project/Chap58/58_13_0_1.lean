module

public import ReasLib.Topology.Category.ProfiniteGrp.InertiaDiagram
import StacksCheckRecall

@[expose] public section

/- 58.13.0.1: the fundamental-group diagram for the strict henselian, henselian, and ordinary
opens and their corresponding spectra. -/
@[stacks 0BSV] #check
  (EtaleFundamentalGroup.InertiaDiagram :
    ProfiniteGrp → ProfiniteGrp → ProfiniteGrp → ProfiniteGrp → ProfiniteGrp → Type)
