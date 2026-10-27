/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Associated
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Quasicoherent
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Sheafification.Fppf
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Restriction

/-! # Topology transport of modules on a category fibred in groupoids -/

@[expose] public section

set_option backward.privateInPublic true

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Étale modules give fppf modules by coefficient transport and fppf sheafification. -/
def fromEtaleModules (X : GroupoidsOver S) :
    etaleModules X ⥤ RingedSite.ModuleCat.{u} (ringedSite X) :=
  SheafOfModules.forget _ ⋙
    PresheafOfModules.restrictScalars (fppfToEtaleStructurePresheafIso X).hom ⋙
      PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf X).obj)

/-- The underlying presheaf of reverse topology transport is the fppf sheafification
of the coefficient-transported étale module presheaf. -/
theorem fromEtaleModules_obj (X : GroupoidsOver S) (M : etaleModules X) :
    ((fromEtaleModules X).obj M).val =
      ((PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf X).obj)).obj
        ((PresheafOfModules.restrictScalars
          (fppfToEtaleStructurePresheafIso X).hom).obj M.val)).val := rfl

/-- Canonical transport from fppf modules to étale modules preserves quasi-coherence. -/
theorem toEtaleModules_preservesQuasicoherent (X : GroupoidsOver S)
    (M : RingedSite.ModuleCat.{u} (ringedSite X)) (hM : M.IsQuasicoherent) :
    ((toEtaleModules X).obj M).IsQuasicoherent := by
  sorry

/-- Coefficient transport followed by fppf sheafification preserves quasi-coherence. -/
theorem fromEtaleModules_preservesQuasicoherent (X : GroupoidsOver S)
    (M : etaleModules X) (hM : M.IsQuasicoherent) :
    ((fromEtaleModules X).obj M).IsQuasicoherent := by
  sorry

private def etaleCoefficientRoundTrip (X : GroupoidsOver S)
    (M : PresheafOfModules.{u} (etaleStructureSheaf X).obj) :
    (PresheafOfModules.restrictScalars (fppfToEtaleStructurePresheafIso X).inv).obj
        ((PresheafOfModules.restrictScalars
          (fppfToEtaleStructurePresheafIso X).hom).obj M) ≅ M :=
  (PresheafOfModules.Restriction.compIso'
    (fppfToEtaleStructurePresheafIso X).inv
    (fppfToEtaleStructurePresheafIso X).hom (𝟙 _)
    (fppfToEtaleStructurePresheafIso X).inv_hom_id.symm).app M ≪≫
      ((PresheafOfModules.Restriction.idIso _).app M).symm

private def fppfCoefficientRoundTrip (X : GroupoidsOver S)
    (M : PresheafOfModules.{u} (structureSheaf X).obj) :
    (PresheafOfModules.restrictScalars (fppfToEtaleStructurePresheafIso X).hom).obj
        ((PresheafOfModules.restrictScalars
          (fppfToEtaleStructurePresheafIso X).inv).obj M) ≅ M :=
  (PresheafOfModules.Restriction.compIso'
    (fppfToEtaleStructurePresheafIso X).hom
    (fppfToEtaleStructurePresheafIso X).inv (𝟙 _)
    (fppfToEtaleStructurePresheafIso X).hom_inv_id.symm).app M ≪≫
      ((PresheafOfModules.Restriction.idIso _).app M).symm

/-- The étale round-trip comparison is the coefficient-transported fppf
sheafification unit. -/
def toFromEtaleModulesComparison (X : GroupoidsOver S) (M : etaleModules X) :
    M ⟶ (toEtaleModules X).obj ((fromEtaleModules X).obj M) where
  val := (etaleCoefficientRoundTrip X M.val).inv ≫
    (PresheafOfModules.restrictScalars (fppfToEtaleStructurePresheafIso X).inv).map
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (structureSheaf X).obj)).unit.app
          ((PresheafOfModules.restrictScalars
            (fppfToEtaleStructurePresheafIso X).hom).obj M.val))

/-- The fppf sheafification unit is bijective on sections of a quasi-coherent
étale module. -/
theorem toFromEtaleModulesComparison_bijective (X : GroupoidsOver S)
    (M : etaleModules X) (hM : M.IsQuasicoherent) (x : X.totalᵒᵖ) :
    Function.Bijective ((toFromEtaleModulesComparison X M).val.app x) := by
  sorry

private def inverseSection {R : Type u} [Ring R] {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (y : N) : M := by
  classical
  exact if h : ∃ x, f x = y then h.choose else 0

private theorem inverseSection_left {R : Type u} [Ring R]
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (hf : Function.Bijective f) :
    Function.LeftInverse (inverseSection f) f := by
  intro x
  dsimp [inverseSection]
  rw [dif_pos ⟨x, rfl⟩]
  exact hf.1 (Exists.choose_spec (⟨x, rfl⟩ : ∃ y, f y = f x))

private theorem inverseSection_right {R : Type u} [Ring R]
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (hf : Function.Bijective f) :
    Function.RightInverse (inverseSection f) f := by
  intro y
  dsimp [inverseSection]
  rw [dif_pos (hf.2 y)]
  exact Exists.choose_spec (hf.2 y)

private def inverseModuleHom {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    (hf : ∀ x, Function.Bijective (f.val.app x)) : N ⟶ M where
  val :=
    { app x := ModuleCat.ofHom
        ((f.val.app x).hom.inverse (inverseSection (f.val.app x))
          (inverseSection_left _ (hf x)) (inverseSection_right _ (hf x)))
      naturality := by
        intro x y a
        ext s
        apply (hf y).1
        change (f.val.app y) (inverseSection (f.val.app y) ((N.val.map a) s)) =
          (f.val.app y) ((M.val.map a) (inverseSection (f.val.app x) s))
        rw [inverseSection_right _ (hf y)]
        rw [PresheafOfModules.naturality_apply]
        rw [inverseSection_right _ (hf x)] }

private def toFromEtaleModulesInverse (X : GroupoidsOver S)
    (M : etaleModules X) (hM : M.IsQuasicoherent) :
    (toEtaleModules X).obj ((fromEtaleModules X).obj M) ⟶ M :=
  inverseModuleHom (toFromEtaleModulesComparison X M)
    (toFromEtaleModulesComparison_bijective X M hM)

/-- The sectionwise inverse to the quasi-coherent round-trip comparison satisfies
both inverse identities. -/
theorem toFromEtaleModulesIso_laws (X : GroupoidsOver S)
    (M : etaleModules X) (hM : M.IsQuasicoherent) :
    (toFromEtaleModulesComparison X M ≫ toFromEtaleModulesInverse X M hM = 𝟙 M) ∧
      (toFromEtaleModulesInverse X M hM ≫ toFromEtaleModulesComparison X M = 𝟙 _) := by
  sorry

/-- An étale module is recovered after the fppf round trip when it is quasi-coherent. -/
def toFromEtaleModulesIso (X : GroupoidsOver S)
    (M : etaleModules X) (hM : M.IsQuasicoherent) :
    M ≅ (toEtaleModules X).obj ((fromEtaleModules X).obj M) where
  hom := toFromEtaleModulesComparison X M
  inv := toFromEtaleModulesInverse X M hM
  hom_inv_id := (toFromEtaleModulesIso_laws X M hM).1
  inv_hom_id := (toFromEtaleModulesIso_laws X M hM).2

private def fromToEtaleModulesComponent (X : GroupoidsOver S)
    (M : RingedSite.ModuleCat.{u} (ringedSite X)) :
    (fromEtaleModules X).obj ((toEtaleModules X).obj M) ≅ M :=
  (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf X).obj)).mapIso
      (fppfCoefficientRoundTrip X M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (structureSheaf X).obj)).counit).app M

/-- The canonical fppf reflection comparisons commute with module morphisms. -/
theorem fromToEtaleModulesIso_laws (X : GroupoidsOver S)
    {M N : RingedSite.ModuleCat.{u} (ringedSite X)} (f : M ⟶ N) :
    (toEtaleModules X ⋙ fromEtaleModules X).map f ≫
        (fromToEtaleModulesComponent X N).hom =
      (fromToEtaleModulesComponent X M).hom ≫ f := by
  sorry

/-- An fppf module is recovered by the canonical sheafification reflection
after restriction to the étale topology. -/
def fromToEtaleModulesIso (X : GroupoidsOver S) :
    toEtaleModules X ⋙ fromEtaleModules X ≅ 𝟭 _ :=
  NatIso.ofComponents (fromToEtaleModulesComponent X)
    (fun f => fromToEtaleModulesIso_laws X f)

end AlgebraicGeometry.GroupoidsOver
