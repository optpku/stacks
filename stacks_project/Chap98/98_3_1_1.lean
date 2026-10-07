module

public import stacks_project.Chap98.«98_3_1_1_Functor»
import StacksCheckRecall

/-!
# Functoriality of predeformation categories

A 1-morphism of categories fibred in groupoids over a locally Noetherian base induces
a functor of the associated predeformation categories over `ArtinianLocalAlgCat Λ k`.
-/

@[expose] public section

/- 98.3.1.1: a 1-morphism F : X ⟶ Y of categories fibred in groupoids over Over S
induces a functor map F x0 : F_{X, k, x0} ⥤ᵇ F_{Y, k, y0} of categories over
ArtinianLocalAlgCat Λ k, sending x0 ⟶ x to F(x0) ⟶ F(x), where
y0 is residueImage F x0. -/
@[stacks 07WJ]
#check AlgebraicGeometry.GroupoidsOver.Predeformation.map
