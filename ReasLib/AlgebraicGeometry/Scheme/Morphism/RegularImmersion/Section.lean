/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Sections

/-!
# Regular immersions of sections
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.Section

variable {X S : Scheme.{u}} {f : X ⟶ S} {σ : S ⟶ X}

/-- A section of a smooth morphism of schemes is a regular immersion. -/
theorem isRegularImmersion [Smooth f] (fac : σ ≫ f = 𝟙 S) :
    IsRegularImmersion σ := sorry

end AlgebraicGeometry.Scheme.Hom.Section
