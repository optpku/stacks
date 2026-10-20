module

public import ReasLib.Topology.Sheaf.ExtensionByInitial
import StacksCheckRecall

@[expose] public section

open TopCat TopologicalSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

section

variable {X : TopCat.{u}} (U : Opens X)

/- Lemma 6.31.10 (1): extension by zero of sheaves of abelian groups along an open inclusion is
fully faithful. -/
@[stacks 00A9 "fully faithful extension by zero"]
#check
  (TopCat.Sheaf.ExtensionByInitial.Properties.fullyFaithful
    (C := AddCommGrpCat.{u}) U :
      (TopCat.Sheaf.ExtensionByInitial.functor (C := AddCommGrpCat.{u}) U).FullyFaithful)

/- Lemma 6.31.10 (2): a sheaf of abelian groups lies in the essential image of extension by zero
from an open subset exactly when its stalks away from that subset are zero. -/
@[stacks 00A9 "zero-stalk essential image"]
#check
  (TopCat.Sheaf.ExtensionByInitial.AddCommGrp.essImage_iff U :
    ∀ 𝒢 : X.Sheaf AddCommGrpCat.{u},
      (TopCat.Sheaf.ExtensionByInitial.functor U).essImage 𝒢 ↔
        ∀ x : X, x ∉ (U : Set X) → IsZero (𝒢.presheaf.stalk x))

end
