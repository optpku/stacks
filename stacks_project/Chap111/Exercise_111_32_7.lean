module

public import ReasLib.Topology.Sheaf.ExtensionByInitial.Generators
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
universe u

/- Exercise 111.32.7: every abelian sheaf is a quotient of a possibly large direct sum of
extensions by the initial object of constant integer sheaves on open subspaces. -/
@[stacks 028N] #check
  (TopCat.Sheaf.ExtensionByInitial.AddCommGrp.existsEpiFromCoproduct.{u} :
    ∀ {X : TopCat.{u}}
      [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
      (F : X.Sheaf AddCommGrpCat.{u}),
      ∃ (I : Type u) (U : I → Opens X)
        (φ : (∐ fun i : I ↦
          TopCat.Sheaf.ExtensionByInitial.AddCommGrp.constantInteger (U i)) ⟶ F), Epi φ)

end
