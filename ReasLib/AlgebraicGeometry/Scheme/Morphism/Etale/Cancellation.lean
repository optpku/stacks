/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Basic

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Etale

/-- A scheme morphism is étale if its composite with an unramified morphism is étale. -/
theorem of_comp_of_unramified {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [Etale (f ≫ g)] [Unramified g] : Etale f := Etale.of_comp f g

end AlgebraicGeometry.Etale
