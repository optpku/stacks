module

public import ReasLib.Topology.Sheaf.ExtensionByInitial
import StacksCheckRecall

@[expose] public section

open TopCat TopologicalSpace

noncomputable section

universe u

section

variable {X : TopCat.{u}} (U : Opens X)

/- Lemma 6.31.9 (1): extension by the empty type along an open inclusion is fully faithful on
sheaves of types. -/
@[stacks 00A8 "full faithfulness of extension by the empty type"]
#check
  (TopCat.Sheaf.ExtensionByInitial.Properties.fullyFaithful
    (C := Type u) U)

/- Lemma 6.31.9 (2): a sheaf of types lies in the essential image of extension by the empty type
exactly when all stalks outside the open subset are empty. -/
@[stacks 00A8 "essential image characterized by empty outside stalks"]
#check
  (TopCat.Sheaf.ExtensionByInitial.Type.essImage_iff U)

end
