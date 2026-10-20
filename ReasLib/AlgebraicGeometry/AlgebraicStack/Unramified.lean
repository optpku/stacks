/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSmoothLocal.Unramified
public import ReasLib.AlgebraicGeometry.AlgebraicStack.EtaleSmoothLocal

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism `f : X ⟶ Y` of algebraic stacks is unramified if it is DM and
has the étale-smooth-local-on-source-and-target lift of unramified morphisms of
algebraic spaces. -/
class Unramified {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop
    extends DM f where
  /-- The étale-smooth-local-on-source-and-target lift of unramified holds for
  `f`. -/
  hasEtaleSmoothLocal :
    hasEtaleSmoothLocalAtSourceAndTarget (@AlgebraicSpace.Unramified S) f

/-- A morphism of algebraic stacks is unramified if and only if it is DM and
has the étale-smooth-local-on-source-and-target lift of unramified. -/
theorem unramified_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Unramified f ↔
      DM f ∧
        hasEtaleSmoothLocalAtSourceAndTarget (@AlgebraicSpace.Unramified S) f :=
  sorry

namespace Unramified

/-- The identity morphism of an algebraic stack is unramified. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    Unramified (𝟙 X) :=
  sorry

/-- An unramified morphism of algebraic stacks has the
étale-smooth-local-on-source-and-target lift of unramified. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Unramified f] :
    hasEtaleSmoothLocalAtSourceAndTarget (@AlgebraicSpace.Unramified S) f :=
  sorry

end Unramified

end AlgebraicGeometry.AlgebraicStack
