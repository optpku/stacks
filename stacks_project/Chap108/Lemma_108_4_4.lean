/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import stacks_project.Chap99.Lemma_99_5_2
public import stacks_project.Chap108.Lemma_108_4_4_Map

/-!
# Lemma 108.4.4

A quasi-finite morphism of separated finite-presentation algebraic spaces over
`B` induces a morphism of stacks of coherent sheaves by fibrewise pushforward.
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

/-- Lemma 108.4.4: if `π : X ⟶ Y` is a quasi-finite morphism of algebraic spaces
which are separated and of finite presentation over an algebraic space `B`, then
`π_*` induces a morphism of stacks `map π y : toGroupoids (π ≫ y) ⟶ toGroupoids y`
over `Over S`, sending `(T ⟶ B, F)` to `(T ⟶ B, π_{T,*} F)`. -/
@[stacks 0DN9]
def map (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] :
    toGroupoids (π ≫ y) ⟶ toGroupoids y :=
  ofBasedFunctor (BasedFunctor.ofFunctor (mapFunctor π y) (mapFunctor_p π y))

/-- Forgetting `map` to based functors recovers `BasedFunctor.ofFunctor` of
`mapFunctor`. -/
theorem map.toBasedFunctor (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] :
    FiberedCategoryOver.Groupoids.toBasedFunctor (map π y) =
      BasedFunctor.ofFunctor (mapFunctor π y) (mapFunctor_p π y) :=
  sorry

/-- The induced morphism of stacks lies strictly over `Over S`. -/
theorem map_p (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] :
    FiberedCategoryOver.Groupoids.toFunctor (map π y) ⋙ p y = p (π ≫ y) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
