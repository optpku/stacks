/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

/-!
# Bounded-below coherent and quasicoherent derived objects

This module gives the canonical inclusion of bounded-below derived objects with coherent
cohomology into those with quasicoherent cohomology on a locally Noetherian scheme.
-/

@[expose] public section

open CategoryTheory
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- Coherent cohomology on a locally Noetherian scheme is quasicoherent cohomology. -/
theorem coherentCohomology_le_quasicoherentCohomology (X : Scheme.{u})
    [IsLocallyNoetherian X] :
    DerivedCategory.Plus.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) ≤
      DerivedCategory.Plus.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) := sorry

/-- The canonical inclusion from bounded-below complexes with coherent cohomology to
bounded-below complexes with quasicoherent cohomology. -/
noncomputable def coherentPlusInclusion (X : Scheme.{u}) [IsLocallyNoetherian X] :
    D⁺[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf] ⥤ Plus X :=
  ObjectProperty.FullSubcategory.restrict
    (𝟭 (DerivedCategory.Plus X.Modules))
    (coherentCohomology_le_quasicoherentCohomology X)

/-- The underlying bounded-below derived object of `coherentPlusInclusion X` is unchanged. -/
theorem coherentPlusInclusion_obj_obj (X : Scheme.{u}) [IsLocallyNoetherian X]
    (K : D⁺[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf]) :
    ((coherentPlusInclusion X).obj K).obj = K.obj := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
