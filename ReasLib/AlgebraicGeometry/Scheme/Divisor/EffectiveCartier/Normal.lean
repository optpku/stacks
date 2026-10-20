/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Pullback.AssociatedSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Normal

/-!
# Normal sheaves of effective Cartier divisors

The sheaf associated to an effective Cartier divisor restricts to the normal sheaf of its
canonical closed immersion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalClosed

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {S : Scheme.{u}}

/-- Pulling the sheaf associated to an effective Cartier divisor back to its subscheme gives
the normal sheaf of the canonical closed immersion. -/
noncomputable def normalSheafIso
    (D : S.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι] :
    (Scheme.Modules.pullback D.subschemeι).obj D.associatedSheaf ≅
      Scheme.Hom.normalSheaf D.subschemeι :=
  asIso (D.associatedSheafPullbackComparison D.subschemeι) ≪≫
    (@asIso _ _ _ _
      ((MonoidalClosed.pre
        (Scheme.Hom.Conormal.pullbackIdealComparison D.subschemeι)).app
          (SheafOfModules.unit D.subscheme.ringCatSheaf)) (by
            change IsIso ((MonoidalClosed.internalHom.map
              (Scheme.Hom.Conormal.pullbackIdealComparison D.subschemeι).op).app _)
            letI := Scheme.Hom.Conormal.pullbackIdealComparison_isIso D.subschemeι
            infer_instance)).symm

end AlgebraicGeometry.Scheme.IdealSheafData
