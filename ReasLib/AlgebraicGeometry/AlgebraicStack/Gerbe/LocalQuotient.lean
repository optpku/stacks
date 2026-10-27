/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Action
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action.Trivial
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.SmallStructureMap
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/-!
# Local classifying presentations of gerbes of algebraic stacks

A morphism of algebraic stacks is a gerbe over its target if and only if,
after an fppf cover of the target by an algebraic space, it becomes the
classifying stack of a flat, locally finitely presented group algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicStack
open GroupoidAlgebraicSpace GroupAlgebraicSpace
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The source of `p : X ⟶ U.toGroupoids` is equivalent over `U` to the
classifying stack of the trivial action of `G`. -/
def IsTrivialActionQuotientOver {S : Scheme.{u}} {U : AlgebraicSpace S}
    {X : GroupoidsOver S} (p : X ⟶ U.toGroupoids)
    (G : GroupAlgebraicSpace U) : Prop :=
  ∃ e : X ≌ SmallQuotient.quotientStack (ofAction G (trivialAction G)),
    Nonempty
      (e.hom ≫ SmallQuotient.toBase (ofAction G (trivialAction G)) ≅ p)

namespace Gerbe

/-- A morphism of algebraic stacks is a gerbe over its target if and only if
an fppf algebraic-space cover of its target makes it equivalent over that cover
to the trivial-action quotient by a flat, locally finitely presented group
algebraic space. -/
theorem iff_exists_trivialQuotient {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (π : X ⟶ Y) :
    Gerbe π ↔
      ∃ (U : AlgebraicSpace S) (G : GroupAlgebraicSpace U)
        (g : U.toGroupoids ⟶ Y),
        AlgebraicSpace.Flat G.X.hom ∧
          AlgebraicSpace.LocallyOfFinitePresentation G.X.hom ∧
          Surjective g ∧ Flat g ∧ LocallyOfFinitePresentation g ∧
            IsTrivialActionQuotientOver
              (TwoFibreProduct.snd.{u + 1, u, u + 1, u} π g) G := sorry

end Gerbe

end AlgebraicGeometry.AlgebraicStack
