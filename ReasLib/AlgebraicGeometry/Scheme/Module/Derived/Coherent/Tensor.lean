/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic

@[expose] public section

/-!
# Coherent cohomology under derived tensor

On a locally Noetherian scheme, the derived tensor product preserves bounded-above
complexes with coherent cohomology.
-/

open AlgebraicGeometry CategoryTheory
open DerivedCategory.TStructure
open scoped RingedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- The derived tensor product of bounded-above complexes with coherent cohomology on a
locally Noetherian scheme is again bounded above with coherent cohomology. -/
theorem derivedTensor_boundedAbove_cohomology_coherent
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (L K : RingedSpace.ModuleDerived X.toRingedSpace)
    (hL_bounded :
      (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) L)
    (hL_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L)
    (hK_bounded :
      (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) K)
    (hK_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) K) :
    (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) (L ⊗^L K) ∧
      DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) (L ⊗^L K) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
