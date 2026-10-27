/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Associated
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction

/-! # Direct commutative coefficient transport on the fppf site -/

@[expose] public section

open AlgebraicGeometry CategoryTheory SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The fppf structure sheaf is the underlying ring sheaf of the commutative
 structure sheaf on the associated fppf site. -/
def commFppfStructureSheafIso (X : GroupoidsOver S) :
    (ringedSite X).structureSheaf ≅
      (commAssociatedRingedSite X .fppf).structureSheaf :=
  (fullyFaithfulSheafToPresheaf (inheritedFppfTopology X) RingCat.{u}).preimageIso
    (associatedToCommStructurePresheafIso X .fppf)

/-- Direct restriction of scalars identifies fppf modules with modules over the
 commutative fppf structure sheaf. -/
def commFppfModulesEquivalence (X : GroupoidsOver S) :
    RingedSite.ModuleCat.{u} (ringedSite X) ≌ commAssociatedModules X .fppf :=
  SheafOfModules.Restriction.equivalenceOfIso (commFppfStructureSheafIso X)

/-- Transport to commutative fppf coefficients by direct restriction of scalars. -/
def toCommFppfModules (X : GroupoidsOver S) :
    RingedSite.ModuleCat.{u} (ringedSite X) ⥤ commAssociatedModules X .fppf :=
  (commFppfModulesEquivalence X).functor

/-- Direct coefficient transport restricts the underlying module presheaf along
 the inverse structure-presheaf identification. -/
theorem toCommFppfModules_obj (X : GroupoidsOver S)
    (F : RingedSite.ModuleCat.{u} (ringedSite X)) :
    ((toCommFppfModules X).obj F).val =
      (PresheafOfModules.restrictScalars
        (associatedToCommStructurePresheafIso X .fppf).inv).obj F.val := rfl

/-- Transport from commutative fppf coefficients by direct restriction of scalars. -/
def fromCommFppfModules (X : GroupoidsOver S) :
    commAssociatedModules X .fppf ⥤ RingedSite.ModuleCat.{u} (ringedSite X) :=
  (commFppfModulesEquivalence X).inverse

/-- Inverse coefficient transport restricts the underlying module presheaf along
 the forward structure-presheaf identification. -/
theorem fromCommFppfModules_obj (X : GroupoidsOver S)
    (F : commAssociatedModules X .fppf) :
    ((fromCommFppfModules X).obj F).val =
      (PresheafOfModules.restrictScalars
        (associatedToCommStructurePresheafIso X .fppf).hom).obj F.val := rfl

/-- Transport to fppf coefficients and back recovers the original commutative
 module sheaf by the coefficient equivalence counit. -/
def toFromCommFppfModulesIso {X : GroupoidsOver S}
    (M : commAssociatedModules X .fppf) :
    (toCommFppfModules X).obj ((fromCommFppfModules X).obj M) ≅ M :=
  (commFppfModulesEquivalence X).counitIso.app M

end AlgebraicGeometry.GroupoidsOver
