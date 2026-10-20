/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Restriction
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 30.10.5: for a Noetherian scheme, restriction to the complement of an ideal
support identifies the colimit of `Hom(I^n𝒢, ℱ)` with `Hom(𝒢|_U, ℱ|_U)`. -/
@[stacks 01YB] #check
  (AlgebraicGeometry.Scheme.Modules.idealPowerProductHomColimitToRestriction_isIso :
    ∀ {X : Scheme.{u}} [IsNoetherian X]
      (I : X.IdealSheafData) (𝒢 ℱ : X.Modules)
      [𝒢.IsCoherent] [ℱ.IsQuasicoherent],
      IsIso
        (AlgebraicGeometry.Scheme.Modules.idealPowerProductHomColimitToRestriction I 𝒢 ℱ))

/- The structure-sheaf specialization identifies the ideal-power Hom colimit with sections
on the complement of the ideal support. -/
#check
  (AlgebraicGeometry.Scheme.Modules.idealSheafPowerHomColimitToComplementSections_isIso_of_isNoetherian :
    ∀ {X : Scheme.{u}} [IsNoetherian X]
      (I : X.IdealSheafData) (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      IsIso
        (AlgebraicGeometry.Scheme.Modules.idealSheafPowerHomColimitToComplementSections I ℱ))
