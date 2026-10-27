/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action.Trivial
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Action
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic

/-!
# Algebraicity of trivial-action quotient stacks

The quotient stack of the trivial action of a group algebraic space over `B` is
algebraic exactly when its structural morphism to `B` is flat and locally of
finite presentation.
-/

@[expose] public section

open AlgebraicGeometry
open GroupoidAlgebraicSpace

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- The quotient stack of the trivial action of a group algebraic space `G` on
`B` is algebraic if and only if `G.X.hom` is flat and locally of finite
presentation. -/
theorem isAlgebraicStack_trivialAction_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) :
    AlgebraicStack (SmallQuotient.quotientStack (ofAction G (trivialAction G))) ↔
      AlgebraicSpace.Flat G.X.hom ∧
        AlgebraicSpace.LocallyOfFinitePresentation G.X.hom := sorry

/-- If `G.X.hom` is flat and locally of finite presentation, then the quotient
stack of the trivial `G`-action on `B` is an algebraic stack. -/
instance instAlgebraicStack_trivialAction {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) [AlgebraicSpace.Flat G.X.hom]
    [AlgebraicSpace.LocallyOfFinitePresentation G.X.hom] :
    AlgebraicStack (SmallQuotient.quotientStack (ofAction G (trivialAction G))) := sorry

/-- If the quotient stack of the trivial `G`-action on `B` is algebraic, then
`G.X.hom` is flat. -/
theorem flat_hom_of_isAlgebraicStack_trivialAction {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (h_algebraic : AlgebraicStack
      (SmallQuotient.quotientStack (ofAction G (trivialAction G)))) :
    AlgebraicSpace.Flat G.X.hom := sorry

/-- If the quotient stack of the trivial `G`-action on `B` is algebraic, then
`G.X.hom` is locally of finite presentation. -/
theorem locallyOfFinitePresentation_hom_of_isAlgebraicStack_trivialAction
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (h_algebraic : AlgebraicStack
      (SmallQuotient.quotientStack (ofAction G (trivialAction G)))) :
    AlgebraicSpace.LocallyOfFinitePresentation G.X.hom := sorry

/-- For the trivial `G`-action on `B`, flatness of `G.X.hom` is equivalent to
flatness of the associated action groupoid. -/
theorem flat_hom_iff_flat_ofAction {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) :
    AlgebraicSpace.Flat G.X.hom ↔
      GroupoidAlgebraicSpace.Flat (ofAction G (trivialAction G)) := sorry

/-- For the trivial `G`-action on `B`, local finite presentation of `G.X.hom` is
equivalent to local finite presentation of the associated action groupoid. -/
theorem locallyOfFinitePresentation_hom_iff_ofAction {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) :
    AlgebraicSpace.LocallyOfFinitePresentation G.X.hom ↔
      GroupoidAlgebraicSpace.LocallyOfFinitePresentation
        (ofAction G (trivialAction G)) := sorry

end AlgebraicGeometry.GroupAlgebraicSpace
