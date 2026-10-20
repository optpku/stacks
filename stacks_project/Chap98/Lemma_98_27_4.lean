module

public import stacks_project.Chap98.Lemma_98_27_4_Functor
public import stacks_project.Chap98.Lemma_98_27_4_Triple
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 98.27.4: in Situation 98.27.1 the rule F sending a locally Noetherian
scheme V over S to the set of compatible triples (Z, u', hatx), and sending a
morphism φ : V2 ⟶ V1 of locally Noetherian schemes over S to the map given by
inverse image of the closed subset, restriction of the open morphism, and
completion of φ, is a contravariant functor. -/
@[stacks 0GHA]
#check (AlgebraicGeometry.AlgebraicSpace.ContractionSituation.functor :
  ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    (σ : AlgebraicGeometry.AlgebraicSpace.ContractionSituation S),
    (AlgebraicGeometry.Scheme.Over.locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1))
