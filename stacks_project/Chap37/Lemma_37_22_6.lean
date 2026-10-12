/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay.BaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 37.22.6 (1): Cohen--Macaulayness at a point ascends through a locally
finite-type base change when the original morphism has locally Noetherian fibres. -/
@[stacks 045T] #check
  (AlgebraicGeometry.Scheme.Hom.CohenMacaulayAt.pullback_of_isPullback :
    ∀ {X' X Y' Y : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
      (h_fibers : LocallyNoetherianFibers f) [LocallyOfFiniteType g]
      (x' : X'), f.CohenMacaulayAt (g' x') → f'.CohenMacaulayAt x')

/- Lemma 37.22.6 (2): Cohen--Macaulayness descends from a base change at a
point where the original morphism is flat. -/
@[stacks 045T] #check
  (AlgebraicGeometry.Scheme.Hom.CohenMacaulayAt.of_isPullback_of_flatAt :
    ∀ {X' X Y' Y : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
      (h_fibers : LocallyNoetherianFibers f) [LocallyOfFiniteType g]
      (x' : X'), f.flatAt (g' x') → f'.CohenMacaulayAt x' →
        f.CohenMacaulayAt (g' x'))

/- Lemma 37.22.6 (3): Cohen--Macaulayness descends from a base change when the
base morphism is flat at the image of the chosen point. -/
@[stacks 045T] #check
  (AlgebraicGeometry.Scheme.Hom.CohenMacaulayAt.of_isPullback_of_flatAt_base :
    ∀ {X' X Y' Y : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
      (h_fibers : LocallyNoetherianFibers f) [LocallyOfFiniteType g]
      (x' : X'), g.flatAt (f' x') → f'.CohenMacaulayAt x' →
        f.CohenMacaulayAt (g' x'))
