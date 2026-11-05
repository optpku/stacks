/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FunctionField.Meromorphic
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Sections
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.OverSections

/-!
# Meromorphic sections determined by generic stalk vectors

On an integral scheme, the generic germ determines a global meromorphic section
of a quasicoherent module. Inverting this fixed germ map extends a given vector
in the generic module stalk to a meromorphic section.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- The generic germ of a global meromorphic section of a module sheaf. -/
def meromorphicSectionGenericGerm (ℱ : X.Modules) :
    X.toLocallyRingedSpace.meromorphicSections ℱ →
      (SheafOfModules.stalkFunctorOfCommRing
        X.toLocallyRingedSpace.meromorphicFunctionSheaf (genericPoint X)).obj
          (X.toLocallyRingedSpace.meromorphicSectionSheaf ℱ) :=
  fun s => SheafOfModules.sectionGermOfCommRing s (genericPoint X)

set_option backward.isDefEq.respectTransparency false in
/-- Taking the generic germ bijects global meromorphic sections of a quasicoherent
module with the generic stalk of its meromorphic scalar extension. -/
theorem meromorphicSectionGenericGerm_bijective (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    Function.Bijective (X.meromorphicSectionGenericGerm ℱ) := by
  let htop : CategoryTheory.Limits.IsTerminal
      (⊤ : TopologicalSpace.Opens X.toTopCat) :=
    CategoryTheory.Limits.IsTerminal.ofUnique _
  have hev : Function.Bijective
      (fun s : X.toLocallyRingedSpace.meromorphicSections ℱ ↦
        s.1 (Opposite.op ⊤)) := by
    let ev := PresheafOfModules.sectionsEquivTerminal
      (X.toLocallyRingedSpace.meromorphicSectionSheaf ℱ).val ⊤ htop
    have he (s : X.toLocallyRingedSpace.meromorphicSections ℱ) :
        ev s = s.1 (Opposite.op ⊤) :=
      PresheafOfModules.sectionsEquivTerminal_apply _ ⊤ htop s
    constructor
    · intro s t h
      exact ev.injective ((he s).trans (h.trans (he t).symm))
    · intro m
      exact ⟨ev.symm m, (he (ev.symm m)).symm.trans (ev.apply_symm_apply m)⟩
  exact (meromorphicSectionSheaf_genericGerm_bijective ℱ).comp hev

/-- Scalar extension to meromorphic sections is injective on the generic stalk. -/
theorem meromorphicSectionStalkMap_generic_injective (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] :
    Function.Injective
      (X.toLocallyRingedSpace.meromorphicSectionStalkMap ℱ (genericPoint X)) := sorry

/-- A generic module vector extends to the meromorphic section obtained by
inverting the generic germ map after meromorphic scalar extension. -/
def meromorphicSectionOfGenericStalk (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (v : RingedSpace.stalkModuleCat ℱ (genericPoint X)) :
    X.toLocallyRingedSpace.meromorphicSections ℱ :=
  Function.invFun (X.meromorphicSectionGenericGerm ℱ)
    (X.toLocallyRingedSpace.meromorphicSectionStalkMap ℱ (genericPoint X) v)

/-- The meromorphic extension of a generic vector has its prescribed generic germ. -/
theorem meromorphicSectionOfGenericStalk_germ (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (v : RingedSpace.stalkModuleCat ℱ (genericPoint X)) :
    SheafOfModules.sectionGermOfCommRing (X.meromorphicSectionOfGenericStalk ℱ v)
        (genericPoint X) =
      X.toLocallyRingedSpace.meromorphicSectionStalkMap ℱ (genericPoint X) v :=
  Function.rightInverse_invFun (X.meromorphicSectionGenericGerm_bijective ℱ).surjective _

/-- A meromorphic section with the prescribed generic germ is the extension of that vector. -/
theorem meromorphicSectionOfGenericStalk_unique (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (v : RingedSpace.stalkModuleCat ℱ (genericPoint X))
    (s : X.toLocallyRingedSpace.meromorphicSections ℱ)
    (hs : SheafOfModules.sectionGermOfCommRing s (genericPoint X) =
      X.toLocallyRingedSpace.meromorphicSectionStalkMap ℱ (genericPoint X) v) :
    s = X.meromorphicSectionOfGenericStalk ℱ v := by
  apply (X.meromorphicSectionGenericGerm_bijective ℱ).injective
  exact hs.trans (X.meromorphicSectionOfGenericStalk_germ ℱ v).symm

/-- The meromorphic extension of a nonzero generic module vector is nonzero. -/
theorem meromorphicSectionOfGenericStalk_ne_zero (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (v : RingedSpace.stalkModuleCat ℱ (genericPoint X)) (hv : v ≠ 0) :
    X.meromorphicSectionOfGenericStalk ℱ v ≠ 0 := by
  intro h
  have hg := X.meromorphicSectionOfGenericStalk_germ ℱ v
  rw [h] at hg
  apply hv
  apply X.meromorphicSectionStalkMap_generic_injective ℱ
  have hg0 : SheafOfModules.sectionGermOfCommRing
      (0 : X.toLocallyRingedSpace.meromorphicSections ℱ) (genericPoint X) = 0 := by
    change (TopCat.Presheaf.Γgerm
      (X.toLocallyRingedSpace.meromorphicSectionSheaf ℱ).val.presheaf
      (genericPoint X)) ((0 : X.toLocallyRingedSpace.meromorphicSections ℱ).val
        (Opposite.op ⊤)) = 0
    rw [PresheafOfModules.sections.zero_eval]
    exact (TopCat.Presheaf.Γgerm
      (X.toLocallyRingedSpace.meromorphicSectionSheaf ℱ).val.presheaf
      (genericPoint X)).hom.map_zero
  have hs0 : X.toLocallyRingedSpace.meromorphicSectionStalkMap ℱ
      (genericPoint X) 0 = 0 := by
    unfold LocallyRingedSpace.meromorphicSectionStalkMap
    exact map_zero _
  exact (hg.symm.trans hg0).trans hs0.symm

end AlgebraicGeometry.Scheme
