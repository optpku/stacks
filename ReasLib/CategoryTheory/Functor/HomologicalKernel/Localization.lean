/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.HomologicalKernel.Retract
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient.Kernel

@[expose] public section

/-!
# Localizing a Homological Functor at Its Kernel

The general Verdier-quotient API accepts an object property `P` together with a comparison
`P ≤ H.homologicalKernel`.  This leaf exposes the common specialization `P = H.homologicalKernel`,
so downstream factorization code does not need to rebuild the reflexive comparison.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open Limits MorphismProperty ObjectProperty Pretriangulated

variable {D : Type u₁} {A : Type u₂}
  [Category.{v₁} D] [Category.{v₂} A]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [Abelian A]

/-- Stacks 05RM: a homological functor inverts the cone-defined morphism property associated to
its homological kernel.  This is the direct input expected by localization lift APIs. -/
@[stacks 05RM "homological functor localizes at its kernel"]
theorem homologicalKernel_trW_isInvertedBy
    (H : D ⥤ A) [H.IsHomological] :
    H.homologicalKernel.trW.IsInvertedBy H := sorry

end CategoryTheory.Functor
