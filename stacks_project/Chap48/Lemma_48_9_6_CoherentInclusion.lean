/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Coherent.Quasicoherent

@[expose] public section

open CategoryTheory
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Compatibility checks for the coherent-to-quasicoherent bounded-below inclusion. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.coherentCohomology_le_quasicoherentCohomology :
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X],
    DerivedCategory.Plus.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) ≤
      DerivedCategory.Plus.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))

#check (AlgebraicGeometry.Scheme.DerivedQCoh.coherentPlusInclusion :
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X],
    D⁺[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf] ⥤ Plus X)

#check (AlgebraicGeometry.Scheme.DerivedQCoh.coherentPlusInclusion_obj_obj :
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X]
    (K : D⁺[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf]),
    ((coherentPlusInclusion X).obj K).obj = K.obj)

end AlgebraicGeometry.Scheme.DerivedQCoh
