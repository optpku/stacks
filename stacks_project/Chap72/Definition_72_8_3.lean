module

public import stacks_project.Chap72.Definition_72_8_3_Alteration
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

/- Definition 72.8.3: Let `S` be a scheme. Let `X` be an integral algebraic space
over `S`. An alteration of `X` is a proper dominant morphism `f : Y ⟶ X` of
algebraic spaces over `S` with `Y` integral such that `f⁻¹(U) ⟶ U` is finite
for some nonempty open `U ⊂ X`. -/
@[stacks 0ADA] #check AlgebraicGeometry.AlgebraicSpace.IsAlteration
#check AlgebraicGeometry.AlgebraicSpace.isAlteration_iff
