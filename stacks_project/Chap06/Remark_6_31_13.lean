module

public import ReasLib.Topology.Sheaf.ExtensionByInitial
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopCat TopologicalSpace

noncomputable section

universe u

section

variable {X : TopCat.{u}} (U : Opens X)
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
variable (ℱ : (TopCat.Opens.Subspace.space U).Sheaf (Type u))

/- Remark 6.31.13 (1): outside an open subset, the stalk of extension by the empty type is
initial, hence empty. -/
@[stacks 00AC "stalk of extension by the empty set outside the open subset"]
#check fun (x : X) (hx : x ∉ (U : Set X)) ↦
  TopCat.Sheaf.ExtensionByInitial.Properties.stalk_isInitial_of_not_mem
    (C := Type u) U ℱ x hx

end

/- Remark 6.31.13 (2): extension by the empty type from a proper open subset does not preserve
terminal objects. -/
@[stacks 00AC "extension by the empty set does not preserve terminal objects"]
recall TopCat.Sheaf.ExtensionByInitial.Type.not_preservesTerminal_of_ne_top

/- Remark 6.31.13 (3): extension by the empty type from a proper open subset is not left exact. -/
@[stacks 00AC "extension by the empty set on sheaves of sets is not left exact"]
recall TopCat.Sheaf.ExtensionByInitial.Type.not_leftExact_of_ne_top

/- Remark 6.31.13 (4): extension by zero on sheaves of abelian groups is exact. -/
@[stacks 00AC "extension by zero on abelian sheaves is exact"]
recall TopCat.Sheaf.ExtensionByInitial.AddCommGrp.exact
