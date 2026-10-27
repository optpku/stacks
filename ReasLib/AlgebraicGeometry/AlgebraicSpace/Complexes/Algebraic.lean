/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Algebraic

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

/-- For a proper, flat morphism of finite presentation between algebraic spaces
over a scheme, the groupoid fibration of relatively perfect complexes with
vanishing negative fibre self-Ext is an algebraic stack. -/
instance instAlgebraicStack {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f] :
    CohStack.AlgebraicStack (toGroupoids f) := sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
