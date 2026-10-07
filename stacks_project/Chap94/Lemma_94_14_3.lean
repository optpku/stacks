module

public import stacks_project.Chap94.Lemma_94_14_3_Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

section
variable {S : Scheme.{u}}
variable {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
variable (f : X ⟶ Z) (g : Y ⟶ Z)

/- Lemma 94.14.3 (1): let `S` be a scheme contained in `Sch_fppf`. Let `X`, `Y`,
`Z` be algebraic stacks over `S`. Let `f : X ⟶ Z`, `g : Y ⟶ Z` be 1-morphisms of
algebraic stacks. Then the 2-fibre product `X ×_{f, Z, g} Y` is an algebraic
stack. -/
@[stacks 04T2]
#check (inferInstance : AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g))
end

section
variable {S : Scheme.{u}}
variable {X Y Z : AlgebraicStacks S}
variable (f : X ⟶ Z) (g : Y ⟶ Z)

/- Lemma 94.14.3 (2): the 2-fibre product `X ×_{f, Z, g} Y` is also the 2-fibre
product in the 2-category of algebraic stacks over `(Sch/S)_fppf`. -/
@[stacks 04T2]
#check (inferInstance : (AlgebraicStacks.twoFibreProduct.cone f g).IsBilimit)
end
