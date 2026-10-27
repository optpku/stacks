/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Restriction.Equivalence
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Sheafification.Fppf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-! # Fppf realization of locally quasi-coherent modules with flat base change -/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Restriction from fppf modules to étale modules admits a left adjoint. -/
instance etaleFppfHom_modulePushforward_isRightAdjoint (X : GroupoidsOver S) :
    (etaleFppfHom X).modulePushforward.{u}.IsRightAdjoint :=
  (@SheafOfModules.PullbackConstruction.adjunction.{u}
    _ _ _ _ _ _ _ _ _ _ (etaleToFppfStructureSheafMap X)
    (PresheafOfModules.Restriction.pushforwardOverIdIsRightAdjointOfIsIso
      (fppfToEtaleStructurePresheafIso X).inv) inferInstance inferInstance).isRightAdjoint

/-- An étale module that is locally quasi-coherent and has flat base change
is a sheaf for the fppf topology. -/
theorem isSheaf_fppf_of_lqcohFbc {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) [IsLocallyQuasiCoherent F] [HasFlatBaseChange F] :
    Presheaf.IsSheaf (ringedSite X).siteTopology
      (etaleModulePresheaf F).presheaf := sorry

namespace LQCohFbc

/-- Fppf realization retains the original module presheaf, transporting its
scalars through the canonical fppf-to-étale structure-presheaf comparison. -/
def toFppf (X : GroupoidsOver S) [AlgebraicStack X] :
    LQCohFbc X ⥤ fppfModules X where
  obj F :=
    { val := etaleModulePresheaf F.obj
      isSheaf := @isSheaf_fppf_of_lqcohFbc S X _ F.obj
        ((lqcohFbc_iff F.obj).mp F.property).1
        ((lqcohFbc_iff F.obj).mp F.property).2 }
  map φ := ⟨(PresheafOfModules.restrictScalars
    (fppfToEtaleStructurePresheaf X)).map φ.hom.val⟩
  map_id F := by
    apply SheafOfModules.hom_ext
    exact (PresheafOfModules.restrictScalars
      (fppfToEtaleStructurePresheaf X)).map_id F.obj.val
  map_comp φ ψ := by
    apply SheafOfModules.hom_ext
    exact (PresheafOfModules.restrictScalars
      (fppfToEtaleStructurePresheaf X)).map_comp φ.hom.val ψ.hom.val

/-- The module presheaf of fppf realization is the scalar-transported
original étale module presheaf. -/
theorem toFppf_obj_val (X : GroupoidsOver S) [AlgebraicStack X] (F : LQCohFbc X) :
    ((toFppf X).obj F).val = etaleModulePresheaf F.obj := rfl

/-- Fppf realization maps a morphism by its original component maps with
the canonical restriction of scalars. -/
theorem toFppf_map_val (X : GroupoidsOver S) [AlgebraicStack X]
    {F G : LQCohFbc X} (φ : F ⟶ G) :
    ((toFppf X).map φ).val =
      (PresheafOfModules.restrictScalars
        (fppfToEtaleStructurePresheaf X)).map φ.hom.val := rfl

/-- Fppf realization is additive. -/
instance toFppf_additive (X : GroupoidsOver S) [AlgebraicStack X] :
    (toFppf X).Additive where
  map_add {F G φ ψ} := by
    apply SheafOfModules.hom_ext
    exact (PresheafOfModules.restrictScalars
      (fppfToEtaleStructurePresheaf X)).map_add

/-- Restricting the fppf realization to the étale topology recovers the
original locally quasi-coherent module with flat base change. -/
theorem toFppf_comp_restriction (X : GroupoidsOver S) [AlgebraicStack X] :
    Nonempty (toFppf X ⋙ restriction X ≅ inclusion X) := sorry

end LQCohFbc

end AlgebraicGeometry.GroupoidsOver

