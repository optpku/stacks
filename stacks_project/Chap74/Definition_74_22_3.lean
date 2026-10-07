module

public import stacks_project.Chap74.Definition_74_22_3_Pseudofunctor
public import stacks_project.Chap74.Definition_74_22_3_DescentData
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v

/- Definition 74.22.3: descent data for algebraic spaces over algebraic spaces with respect
to a family of morphisms of algebraic spaces over a scheme `S` with fixed target, together
with their compatible componentwise morphisms. -/
@[stacks 0ADI] #check
  (@AlgebraicGeometry.AlgebraicSpace.DescentData :
    {I : Type v} → {S : Scheme.{u}} → {X : AlgebraicSpace S} →
      (Xᵢ : I → AlgebraicSpace S) → ((i : I) → Xᵢ i ⟶ X) →
        Type (max (u + 1) v))

#check @AlgebraicGeometry.AlgebraicSpace.DescentData.ofObj
#check @AlgebraicGeometry.AlgebraicSpace.DescentData.Chosen
#check @AlgebraicGeometry.AlgebraicSpace.DescentData.Chosen.ofIso
#check @AlgebraicGeometry.AlgebraicSpace.DescentData.Chosen.iso
#check @AlgebraicGeometry.AlgebraicSpace.DescentData.Chosen.cocycle
#check @AlgebraicGeometry.AlgebraicSpace.DescentData.Chosen.hom_comm
#check @AlgebraicGeometry.AlgebraicSpace.DescentData.Chosen.equivalence
