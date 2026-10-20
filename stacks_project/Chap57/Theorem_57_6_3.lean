/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived.Representability
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.Bounded
open scoped CategoryTheory.Pretriangulated.Opposite
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

/- Theorem 57.6.3: for a proper scheme over a field, every `k`-linear cohomological
   functor on the opposite perfect derived category with finite total shifted values is
   represented by a bounded coherent complex. -/
@[stacks 0FYH]
#check
  (AlgebraicGeometry.SchemeOverField.PerfectDerived.existsBoundedCoherentRepresentation :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [IsProper X.hom] →
      (F : (AlgebraicGeometry.SchemeOverField.PerfectDerived X)ᵒᵖ ⥤ ModuleCat k) →
      [F.IsHomological] → [F.Linear k] →
      (hF_finite : ∀ E : AlgebraicGeometry.SchemeOverField.PerfectDerived X,
        GradedObject.FiniteTotalDimension
          (fun n : ℤ ↦ F.obj (Opposite.op (E⟦n⟧)))) →
      ∃ K : Dᵇ[SheafOfModules.isCoherent X.left.ringCatSheaf],
        Nonempty
          (AlgebraicGeometry.SchemeOverField.PerfectDerived.representedBy X
              ((CohomologyIn.ambient
                (SheafOfModules.isCoherent X.left.ringCatSheaf)).obj K) ≅ F))

end
