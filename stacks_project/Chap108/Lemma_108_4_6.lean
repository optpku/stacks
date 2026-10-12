/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap108.Lemma_108_4_4
public import stacks_project.Chap108.Lemma_108_4_6_ClosedImmersion

/-!
# Lemma 108.4.6

A closed immersion of separated finite-presentation algebraic spaces over `B`
induces a closed immersion of stacks of coherent sheaves.
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

/-- Lemma 108.4.6: if `π : X ⟶ Y` is a closed immersion of algebraic spaces
which are separated and of finite presentation over an algebraic space `B`,
then the morphism `map π y : toGroupoids (π ≫ y) ⟶ toGroupoids y` of
Lemma 108.4.4 is a closed immersion of stacks. -/
@[stacks 0DNB]
instance instClosedImmersion_map (π : X ⟶ Y) (y : Y ⟶ B) [IsClosedImmersion π]
    [QuasiFinite π] [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y] :
    Hom.ClosedImmersion (map π y) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
