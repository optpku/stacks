/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Regular

/-!
# Regularity consequences of étale morphisms
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry.Etale

/-- The source of an étale morphism with reduced target is reduced. -/
theorem isReduced
    {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] [IsReduced X] :
    IsReduced Y := sorry

/-- The source of an étale morphism with regular target is regular. -/
theorem isRegular
    {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] [Scheme.Regular X] :
    Scheme.Regular Y := sorry

end AlgebraicGeometry.Etale
