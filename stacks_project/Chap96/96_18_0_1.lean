module

import StacksCheckRecall
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

variable {S : Scheme.{u}} {U X : GroupoidsOver S} (f : U ⟶ X)

/- 96.18.0.1: a 1-morphism f : 𝒰 ⟶ 𝒳 of categories fibred in groupoids over
(Sch/S)_fppf, drawn as the commuting triangle with projections q = 𝒰.p and
p = 𝒳.p. The Lean 1-cell is f : U ⟶ X in GroupoidsOver S, and the triangle
equation is toFunctor f ⋙ X.p = U.p. Informally 𝒰 is thought of as a covering
of 𝒳. -/
@[stacks 06X4] #check (comm f)

#check (f : U ⟶ X)
#check U.p
#check X.p
