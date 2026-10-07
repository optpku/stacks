module

public import ReasLib.Topology.Sheaves.Types.Sheafification
import StacksCheckRecall

@[expose] public section

open TopCat TopologicalSpace

universe u

variable {X : TopCat.{u}} (F : X.Presheaf (Type u)) (U : Opens X)

/- Lemma 6.18.1: sections of the sheafification over `U` are the pullback of sections of the
presheaf of stalk families and the product of the original stalks over the product of the stalks
of that presheaf. -/
@[stacks 0084]
#check TopCat.Presheaf.sheafifySectionIsPullback F U
