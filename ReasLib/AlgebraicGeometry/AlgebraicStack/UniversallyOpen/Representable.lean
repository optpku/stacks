/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyOpen
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.OpenMap
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct

/-!
# Representable universally open morphisms of algebraic stacks

A morphism of algebraic stacks representable by algebraic spaces is universally
open in the sense of scheme-slice tests of algebraic spaces if and only if
every algebraic-stack base change induces an open map on underlying point
spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- For every morphism of algebraic stacks `Z ⟶ Y`, the 2-fibre-product
projection `Z ×_Y X ⟶ Z` induces an open map of underlying point spaces. -/
def isOpenMapAfterBaseChange {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y),
    AlgebraicStack.pointsIsOpenMap (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)

/-- Being open after every algebraic-stack base change means each canonical
2-fibre-product projection `Z ×_Y X ⟶ Z` induces an open map of underlying
point spaces. -/
theorem isOpenMapAfterBaseChange_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    isOpenMapAfterBaseChange f ↔
      ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y),
        AlgebraicStack.pointsIsOpenMap (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  Iff.rfl

/-- A morphism of algebraic stacks representable by algebraic spaces has
universally open scheme-slice representing morphisms if and only if every
algebraic-stack base change induces an open map on underlying point spaces. -/
@[stacks 06U1]
theorem has_universallyOpen_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.UniversallyOpen S) f ↔ isOpenMapAfterBaseChange f :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
