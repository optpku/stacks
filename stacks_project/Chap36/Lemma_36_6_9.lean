/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.LocalCohomology.KoszulRegular

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpace.ModuleDerived
open SheafOfModules.ClosedSubset.SupportedDerived

noncomputable section

universe u

/- Lemma 36.6.9: local cohomology of a flat quasicoherent module supported on a
Koszul-regular cutout of length `c` vanishes in every degree other than `c`. -/
@[stacks 0G7P] #check
  (AlgebraicGeometry.ClosedSubset.IsKoszulRegularCutout.localCohomologySheaf_isZero :
    ∀ (X : Scheme.{u}) (Z : TopologicalSpace.Closeds X) (c : ℕ)
      (hZ : AlgebraicGeometry.ClosedSubset.IsKoszulRegularCutout Z c)
      (ℱ : X.Modules) [ℱ.IsFlat] [ℱ.IsQuasicoherent]
      (i : ℤ) (hi : i ≠ (c : ℤ)),
      IsZero
        (cohomologySheaf
          ((coreflector X.toRingedSpace.ringCatSheaf Z ⋙
              inclusion X.toRingedSpace.ringCatSheaf Z).obj
            ((ModuleCech.moduleToDerived X).obj ℱ)) i))

end
