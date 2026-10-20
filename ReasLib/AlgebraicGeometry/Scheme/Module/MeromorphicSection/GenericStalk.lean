module

public import ReasLib.AlgebraicGeometry.Scheme.FunctionField.Meromorphic
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Sections

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

/-- Taking the generic germ bijects global meromorphic sections of a quasicoherent
module with the generic stalk of its meromorphic scalar extension. -/
theorem meromorphicSectionGenericGerm_bijective (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    Function.Bijective (X.meromorphicSectionGenericGerm ℱ) := sorry

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
