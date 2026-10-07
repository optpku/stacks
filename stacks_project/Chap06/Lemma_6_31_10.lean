module

public import ReasLib.Topology.Sheaf.ExtensionByInitial
import StacksCheckRecall

@[expose] public section

open TopCat TopologicalSpace

noncomputable section

universe u

section

variable {X : TopCat.{u}} (U : Opens X)

/- Lemma 6.31.10 (1): extension by zero of sheaves of abelian groups along an open inclusion is
fully faithful. -/
@[stacks 00A9 "fully faithful extension by zero"]
#check
  (TopCat.Sheaf.ExtensionByInitial.Properties.fullyFaithful
    (C := AddCommGrpCat.{u}) U)

/- Lemma 6.31.10 (2): a sheaf of abelian groups lies in the essential image of extension by zero
from an open subset exactly when its stalks away from that subset are zero. -/
@[stacks 00A9 "zero-stalk essential image"]
#check
  (TopCat.Sheaf.ExtensionByInitial.AddCommGrp.essImage_iff U)

end
