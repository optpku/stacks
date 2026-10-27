/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Algebraic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

/-- The groupoid fibration of finitely presented quasi-coherent modules on the
fibres of a finitely presented separated morphism of algebraic spaces, flat
over the test scheme with proper support, is an algebraic stack. -/
instance instAlgebraicStackOfSeparated {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [FinitePresentation f] [Separated f] :
    AlgebraicStack (toGroupoids f) := sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
