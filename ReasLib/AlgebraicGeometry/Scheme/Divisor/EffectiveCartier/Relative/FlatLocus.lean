/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative.FlatAt
import Mathlib.Tactic.CrossRefAttribute

/-!
# A flat neighborhood of a relative effective Cartier divisor

A locally finitely presented morphism is flat on an open neighborhood of the support of a
relative effective Cartier divisor.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace IsRelativeEffectiveCartierDivisor

/-- A locally finitely presented morphism is flat on an open neighborhood of the support of a
relative effective Cartier divisor. -/
@[stacks 062V]
theorem exists_flat_openContaining_support_of_locallyOfFinitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) (D : X.IdealSheafData)
    [IsRelativeEffectiveCartierDivisor f D] [LocallyOfFinitePresentation f] :
    ∃ U : X.Opens, (D.support : Set X) ⊆ (U : Set X) ∧ Flat (U.ι ≫ f) := sorry

end IsRelativeEffectiveCartierDivisor
end AlgebraicGeometry
