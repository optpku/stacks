/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Diagonal

/-!
# Sections of unramified scheme morphisms
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.Section

variable {X S : Scheme.{u}} {f : X ⟶ S} {s : S ⟶ X}

/-- A section of an unramified morphism of schemes is an open immersion. -/
theorem isOpenImmersion [Unramified f] (fac : s ≫ f = 𝟙 S) :
    IsOpenImmersion s := sorry

/-- A section of an unramified separated morphism of schemes is both an open immersion and
a closed immersion. -/
theorem isOpenImmersion_and_isClosedImmersion [Unramified f] [IsSeparated f]
    (fac : s ≫ f = 𝟙 S) : IsOpenImmersion s ∧ IsClosedImmersion s := sorry

end AlgebraicGeometry.Scheme.Hom.Section
