module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap71.Lemma_71_4_6_Fiber
public import stacks_project.Chap76.Lemma_76_26_3_CohenMacaulay

/-!
# Base change of Cohen--Macaulay morphisms of algebraic spaces

In a cartesian square of algebraic spaces, Cohen--Macaulayness at a point
ascends along a locally finite-type base change when the original morphism
has locally Noetherian fibres, and descends if either the original morphism
is flat at the image point or the base morphism is flat at the image of the
chosen point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohenMacaulayAt

/-- Lemma 76.26.6 (1): if `f : X ⟶ Y` has locally Noetherian fibres and
`g : Y' ⟶ Y` is locally of finite type, then in a cartesian square Cohen--Macaulayness
of `f` at the image of `x'` implies Cohen--Macaulayness of the base change
`f'` at `x'`. -/
@[stacks 0E0Z]
theorem pullback_of_isPullback {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
    [LocallyNoetherianFibers f] [LocallyOfFiniteType g] (x' : Points X')
    (hcm : CohenMacaulayAt f (Points.map g' x')) :
    CohenMacaulayAt f' x' :=
  sorry

/-- Lemma 76.26.6 (2): if `f : X ⟶ Y` has locally Noetherian fibres and
`g : Y' ⟶ Y` is locally of finite type, then in a cartesian square flatness of
`f` at the image of `x'` together with Cohen--Macaulayness of the base change
`f'` at `x'` imply Cohen--Macaulayness of `f` at that image. -/
@[stacks 0E0Z]
theorem of_isPullback_of_flatAt {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
    [LocallyNoetherianFibers f] [LocallyOfFiniteType g] (x' : Points X')
    (hflat : FlatAt f (Points.map g' x'))
    (hcm : CohenMacaulayAt f' x') :
    CohenMacaulayAt f (Points.map g' x') :=
  sorry

/-- Lemma 76.26.6 (3): if `f : X ⟶ Y` has locally Noetherian fibres and
`g : Y' ⟶ Y` is locally of finite type, then in a cartesian square flatness of
`g` at `Points.map f' x'` together with Cohen--Macaulayness of the base
change `f'` at `x'` imply Cohen--Macaulayness of `f` at `Points.map g' x'`. -/
@[stacks 0E0Z]
theorem of_isPullback_of_flatAt_base {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
    [LocallyNoetherianFibers f] [LocallyOfFiniteType g] (x' : Points X')
    (hflat : FlatAt g (Points.map f' x'))
    (hcm : CohenMacaulayAt f' x') :
    CohenMacaulayAt f (Points.map g' x') :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohenMacaulayAt
