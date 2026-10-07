module

public import ReasLib.Topology.Presheaf.Cech.TermIso
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopCat.Presheaf.Cech AlgebraicTopology

/- 20.9.0.1: evaluating the ordinary Čech differential of an abelian presheaf at a cochain
and tuple recovers the alternating omitted-index restriction formula. -/
@[stacks 01EE]
#check @TopCat.Presheaf.Cech.termIso_hom_d_apply

/- The explicit coordinate payload is the signed sum of omitted-index restrictions. -/
#check @TopCat.Presheaf.Cech.differentialToFun

/- The same identification at the morphism level, before evaluating on cochains. -/
#check @TopCat.Presheaf.Cech.termIso_comm_d

end
