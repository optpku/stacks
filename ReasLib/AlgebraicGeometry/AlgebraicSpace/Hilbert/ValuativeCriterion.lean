/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver.ValuativeCriterion

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The Hilbert functor of a proper morphism of finite presentation satisfies
the existence part of the valuative criterion. -/
instance instExistence (f : X ⟶ B) [FinitePresentation f] [Proper f] :
    SchemeOver.ValuativeCriterion.Existence (hilbert f) := sorry

end AlgebraicGeometry.AlgebraicSpace.Hilbert
