module

public import ReasLib.Topology.Sheaf.Support
import StacksCheckRecall

@[expose] public section

open TopCat TopologicalSpace

universe u

/- The support membership criterion is computed by the germ of the global unit section. -/
#check fun {X : TopCat.{u}} (F : X.Sheaf RingCat.{u}) (x : X) ↦
  TopCat.Sheaf.mem_ringSheafSupport_iff_one_germ_ne_zero F x

/- Lemma 17.5.3 (01AV): the support of a sheaf of rings is closed. -/
@[stacks 01AV]
#check fun {X : TopCat.{u}} (F : X.Sheaf RingCat.{u}) ↦
  (TopCat.Sheaf.isClosed_ringSheafSupport F :
    IsClosed (TopCat.Sheaf.ringSheafSupport F))
