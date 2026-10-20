module

public import ReasLib.Topology.Sheaf.ExtensionByInitial.Presentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open scoped TopCat

noncomputable section

universe u

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
variable (B : Set (Opens X)) (hB : Opens.IsBasis B)
variable (F : TopCat.Sheaf (Type u) X)

/- Lemma 17.19.1: every sheaf of sets on `X` is an epimorphic image of a coproduct of
lower-shriek extensions `j![U i, S i]`, where each `U i` belongs to the chosen basis and each
`S i` is finite. -/
@[stacks 0CAH]
#check
  (TopCat.Sheaf.ExtensionByInitial.Constant.existsEpiFromBasis B hB F :
    ∃ (I : Type u) (U : I → Opens X) (S : I → Type u)
      (_ : ∀ i, U i ∈ B) (_ : ∀ i, Finite (S i)),
      ∃ phi : (∐ fun i : I ↦ j![U i, S i]) ⟶ F, Epi phi)

/- The reusable owner chooses the canonical index of all basis sections and constructs the
coproduct source and epimorphism explicitly. -/
#check @TopCat.Sheaf.ExtensionByInitial.Constant.BasisSection
#check @TopCat.Sheaf.ExtensionByInitial.Constant.BasisSection.source
#check @TopCat.Sheaf.ExtensionByInitial.Constant.BasisSection.hom
#check @TopCat.Sheaf.ExtensionByInitial.Constant.BasisSection.hom_epi

end

end
