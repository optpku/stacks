/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallySmooth

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Smooth

/-- A scheme morphism is smooth exactly when it is locally of finite presentation and
formally smooth. -/
theorem iff_locallyOfFinitePresentation_and_formallySmooth
    {X S : Scheme.{u}} (f : X ⟶ S) :
    Smooth f ↔ LocallyOfFinitePresentation f ∧ FormallySmooth f := sorry

end AlgebraicGeometry.Smooth
