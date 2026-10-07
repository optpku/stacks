module

public import stacks_project.Chap108.Lemma_108_4_4
public import stacks_project.Chap108.Lemma_108_4_5_OpenImmersion

/-!
# Lemma 108.4.5

An open immersion of separated finite-presentation algebraic spaces over `B`
induces an open immersion of stacks of coherent sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack
open CategoryTheory.BasedCategory CategoryTheory.BasedFunctor
open CategoryTheory.FiberedCategoryOver.Groupoids
open scoped CategoryTheory.BasedFunctor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X Y B : AlgebraicSpace S}

/-- Lemma 108.4.5: if `π : X ⟶ Y` is an open immersion of algebraic spaces
which are separated and of finite presentation over an algebraic space `B`,
then the morphism `map π y : toGroupoids (π ≫ y) ⟶ toGroupoids y` of
Lemma 108.4.4 is an open immersion of stacks. -/
@[stacks 0DNA]
instance instOpenImmersion_map (π : X ⟶ Y) (y : Y ⟶ B) [IsOpenImmersion π]
    [QuasiFinite π] [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y] :
    Hom.OpenImmersion (map π y) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
