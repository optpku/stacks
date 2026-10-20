/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic

/-!
# Pullbacks of algebraic stacks over algebraic spaces

The chosen two-fibre product supplies the base-change object and its projection.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ObjectProperty
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The chosen 2-fibre product `Y' ×_Y X` of a morphism `f : X ⟶ Y.toGroupoids`
from an algebraic stack to an algebraic space, along a morphism `h : Y' ⟶ Y`
of algebraic spaces. -/
abbrev pullback {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y : AlgebraicSpace S} (f : X ⟶ Y.toGroupoids) {Y' : AlgebraicSpace S}
    (h : Y' ⟶ Y) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} f (AlgebraicSpace.toGroupoids.map h)

/-- `pullback f h` is the chosen 2-fibre product of `f` against
`AlgebraicSpace.toGroupoids.map h`. -/
theorem pullback_eq {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y : AlgebraicSpace S} (f : X ⟶ Y.toGroupoids) {Y' : AlgebraicSpace S}
    (h : Y' ⟶ Y) :
    pullback f h =
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} f
        (AlgebraicSpace.toGroupoids.map h) :=
  sorry

/-- The first projection `Y' ×_Y X ⟶ X` of a morphism `f : X ⟶ Y.toGroupoids`
from an algebraic stack to an algebraic space, along a morphism `h : Y' ⟶ Y`
of algebraic spaces. -/
abbrev pullbackFst {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y : AlgebraicSpace S} (f : X ⟶ Y.toGroupoids) {Y' : AlgebraicSpace S}
    (h : Y' ⟶ Y) : pullback f h ⟶ X :=
  TwoFibreProduct.fst.{u + 1, u, u + 1, u} f (AlgebraicSpace.toGroupoids.map h)

/-- `pullbackFst f h` is the first projection of the chosen 2-fibre product of
`f` against `AlgebraicSpace.toGroupoids.map h`. -/
theorem pullbackFst_eq {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y : AlgebraicSpace S} (f : X ⟶ Y.toGroupoids) {Y' : AlgebraicSpace S}
    (h : Y' ⟶ Y) :
    pullbackFst f h =
      TwoFibreProduct.fst.{u + 1, u, u + 1, u} f
        (AlgebraicSpace.toGroupoids.map h) :=
  rfl

/-- The base-changed morphism `f' : Y' ×_Y X ⟶ Y'` associated to
`f : X ⟶ Y.toGroupoids` and `h : Y' ⟶ Y`. -/
abbrev pullbackSnd {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y : AlgebraicSpace S} (f : X ⟶ Y.toGroupoids) {Y' : AlgebraicSpace S}
    (h : Y' ⟶ Y) : pullback f h ⟶ Y'.toGroupoids :=
  TwoFibreProduct.snd.{u + 1, u, u + 1, u} f (AlgebraicSpace.toGroupoids.map h)

/-- `pullbackSnd f h` is the second projection of the chosen 2-fibre product of
`f` against `AlgebraicSpace.toGroupoids.map h`. -/
theorem pullbackSnd_eq {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y : AlgebraicSpace S} (f : X ⟶ Y.toGroupoids) {Y' : AlgebraicSpace S}
    (h : Y' ⟶ Y) :
    pullbackSnd f h =
      TwoFibreProduct.snd.{u + 1, u, u + 1, u} f
        (AlgebraicSpace.toGroupoids.map h) :=
  sorry

/-- The chosen 2-fibre product of an algebraic stack against an algebraic space
is an algebraic stack. -/
instance instAlgebraicStack_pullback {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {Y : AlgebraicSpace S} (f : X ⟶ Y.toGroupoids)
    {Y' : AlgebraicSpace S} (h : Y' ⟶ Y) : AlgebraicStack (pullback f h) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
