/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap71.Lemma_71_4_6_Fiber
public import stacks_project.Chap76.Lemma_76_27_6_GorensteinAt

/-!
# Base change of Gorenstein morphisms of algebraic spaces

In a cartesian square of algebraic spaces, Gorensteinness at a point ascends
along a locally finite-type base change when the original morphism has
locally Noetherian fibres, and descends if either the original morphism is
flat at the image point or the base morphism is flat at the image of the
chosen point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GorensteinAt

/-- Lemma 76.27.6 (1): if `f : X ⟶ Y` has locally Noetherian fibres and
`g : Y' ⟶ Y` is locally of finite type, then in a cartesian square
Gorensteinness of `f` at the image of `x'` implies Gorensteinness of the
base change `f'` at `x'`. -/
@[stacks 0E18]
theorem pullback_of_isPullback {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
    [LocallyNoetherianFibers f] [LocallyOfFiniteType g] (x' : Points X')
    (hg : GorensteinAt f (Points.map g' x')) :
    GorensteinAt f' x' :=
  sorry

/-- Lemma 76.27.6 (2): if `f : X ⟶ Y` has locally Noetherian fibres and
`g : Y' ⟶ Y` is locally of finite type, then in a cartesian square flatness
of `f` at the image of `x'` together with Gorensteinness of the base change
`f'` at `x'` imply Gorensteinness of `f` at that image. -/
@[stacks 0E18]
theorem of_isPullback_of_flatAt {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
    [LocallyNoetherianFibers f] [LocallyOfFiniteType g] (x' : Points X')
    (hflat : FlatAt f (Points.map g' x'))
    (hg : GorensteinAt f' x') :
    GorensteinAt f (Points.map g' x') :=
  sorry

/-- Lemma 76.27.6 (3): if `f : X ⟶ Y` has locally Noetherian fibres and
`g : Y' ⟶ Y` is locally of finite type, then in a cartesian square flatness
of `g` at the image of `x'` in `|Y'|` together with Gorensteinness of the
base change `f'` at `x'` imply Gorensteinness of `f` at the image of `x'`. -/
@[stacks 0E18]
theorem of_isPullback_of_flatAt_base {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
    [LocallyNoetherianFibers f] [LocallyOfFiniteType g] (x' : Points X')
    (hflat : FlatAt g (Points.map f' x'))
    (hg : GorensteinAt f' x') :
    GorensteinAt f (Points.map g' x') :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.GorensteinAt
