/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Presheaf
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Stackification

/-!
# The canonical fppf quotient stack of an algebraic-space groupoid

The quotient stack is the stackification of the co-Grothendieck projection of the
groupoid-valued functor of scheme points on the fppf site over the base scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.CategoryOfElements Opposite
open Functor.IsFibered.InGroupoids.Stackification
open CategoryTheory.Pseudofunctor.CoGrothendieck
open scoped CategoryTheory.Pseudofunctor.CoGrothendieck

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The selected stackification presentation of `[U/_p R]` on `(Sch/S)_fppf`. -/
def fppfQuotientStackPresentation {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    Presentation (Scheme.fppfTopology.over S) (groupoidPresheafProjection G.points) :=
  presentation (Scheme.fppfTopology.over S) (groupoidPresheafProjection G.points)

/-- The quotient stack `[U/R]` of a groupoid in algebraic spaces over `B`, as the selected
stackification of `[U/_p R]` on `(Sch/S)_fppf`. -/
def fppfQuotientStack {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  (fppfQuotientStackPresentation G).target

end AlgebraicGeometry.GroupoidAlgebraicSpace
