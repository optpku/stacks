/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.SmallStructureMap
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Algebraic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Action
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open GroupoidAlgebraicSpace GroupAlgebraicSpace
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.SmallQuotient

/-- Flatness of `G ⟶ B` implies flatness of the action groupoid. -/
theorem flat_ofAction {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : GroupAlgebraicSpace.Action G)
    [AlgebraicSpace.Flat G.X.hom] : Flat (ofAction G X) := sorry

/-- Local finite presentation of `G ⟶ B` implies local finite presentation of the
action groupoid. -/
theorem locallyOfFinitePresentation_ofAction {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : GroupAlgebraicSpace.Action G)
    [AlgebraicSpace.LocallyOfFinitePresentation G.X.hom] :
    LocallyOfFinitePresentation (ofAction G X) := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.SmallQuotient

namespace AlgebraicGeometry.AlgebraicStack.Smooth

/-- A flat, locally finitely presented group algebraic space acting on a smooth
algebraic space has a quotient stack smooth over the base algebraic space. -/
theorem ofAction {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (G : GroupAlgebraicSpace Y) (X : Action G)
    [AlgebraicSpace.Smooth X.X.hom] [AlgebraicSpace.Flat G.X.hom]
    [AlgebraicSpace.LocallyOfFinitePresentation G.X.hom] :
    -- Local instance justification (defeq pin): the algebraic-stack smoothness predicate is indexed by the proved algebraicity of this concrete quotient; the explicit action cannot have a companion instance.
    letI : AlgebraicStack (SmallQuotient.quotientStack (GroupoidAlgebraicSpace.ofAction G X)) :=
      isAlgebraicStack_quotientStack_of_flat (GroupoidAlgebraicSpace.ofAction G X)
        (SmallQuotient.flat_ofAction G X) (SmallQuotient.locallyOfFinitePresentation_ofAction G X)
    Smooth (SmallQuotient.toBase (GroupoidAlgebraicSpace.ofAction G X)) := sorry

end AlgebraicGeometry.AlgebraicStack.Smooth
