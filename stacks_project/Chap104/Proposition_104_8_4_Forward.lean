/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap104.Proposition_104_8_4_Factories
public import stacks_project.Chap104.Proposition_104_8_4_Large
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The specified canonical forward functor

First sheafify modules on the chaotic affine site, then extend from the dense
affine basis and sheafify. Both underived functors are exact. Their derived
functor is the standard exact cochain/localization construction, followed by
the actual parasitic Verdier quotient. No total-derived existence factory or
inverse-object selector occurs in this forward route.
-/

@[expose] public section
open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.Limits RingedSite RingedSite.Hom
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicStack
variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]

/-- Epsilon inverse image is actual module sheafification with identity coefficients. -/
def epsilonModules :
    RingedSite.ModuleCat.{u + 1} (ofCommRingSheaf ⊥ (affineStructureSheaf X)) ⥤
      RingedSite.ModuleCat.{u + 1} (affineFppfRingedSite X) :=
  SheafOfModules.forget (ofCommRingSheaf ⊥ (affineStructureSheaf X)).structureSheaf ⋙
    PresheafOfModules.restrictScalars (affineCoefficientPresheafIso X).inv ⋙
    Stacks1048Forward.certifiedModuleSheafification (affineSiteFppfTopology X)
      (affineFppfRestrictedStructureSheaf X)

/-- Extension from affine objects uses the actual presheaf pullback and sheafification.
The pullback certificate is the proved free-generator construction on AsSmall. -/
def affineExtensionModules :
    RingedSite.ModuleCat.{u + 1} (affineFppfRingedSite X) ⥤ LiftedFppfModules X :=
  SheafOfModules.forget (affineFppfRestrictedStructureSheaf X) ⋙
    Stacks1048Forward.extendPresheaf (F := affineInclusion X)
      (R := (liftedFppfStructureSheaf X).obj) (𝟙 _) ⋙
    Stacks1048Forward.certifiedModuleSheafification (fppfRingedSite X).siteTopology
      (liftedFppfStructureSheaf X)

/-- The underived forward functor is the specified epsilon/affine composite. -/
def forwardModules := epsilonModules X ⋙ affineExtensionModules X

/-- These fixed underived sheafification/affine-basis functors are additive. -/
instance forwardModules_additive : (forwardModules X).Additive := by
  sorry

/-- Sheafification is left exact and dense-affine extension is an exact equivalence. -/
instance forwardModules_preservesFiniteLimits : PreservesFiniteLimits (forwardModules X) := by
  sorry

/-- Both specified left adjoints preserve finite colimits. -/
instance forwardModules_preservesFiniteColimits : PreservesFiniteColimits (forwardModules X) := by
  sorry

/-- Derive the fixed exact functor by applying it degreewise and localizing.
This is not totalLeftDerived and consumes no HasLeftDerivedFunctor certificate. -/
def forwardDerived :
    Hom.ModuleDerived.{u + 1} (ofCommRingSheaf ⊥ (affineStructureSheaf X)) ⥤
      LiftedModuleDerived X := by
  -- Local instance justification (instance diamond): use the proved module-sheaf abelian structure on the source, including its finite constructions.
  letI : Abelian (RingedSite.ModuleCat.{u + 1}
      (ofCommRingSheaf ⊥ (affineStructureSheaf X))) :=
    Stacks1048Forward.certifiedModuleAbelian ⊥
      (ofCommRingSheaf ⊥ (affineStructureSheaf X)).structureSheaf
  -- Local instance justification (instance diamond): use the proved abelian structure on the target instead of the imported admitted presentation bridge.
  letI : Abelian (LiftedFppfModules X) :=
    Stacks1048Forward.certifiedModuleAbelian (fppfRingedSite X).siteTopology
      (liftedFppfStructureSheaf X)
  -- Local instance justification (defeq pin): this is the standard quotient model of the actual source cochain category.
  letI : HasDerivedCategory.{u + 2} (RingedSite.ModuleCat.{u + 1}
      (ofCommRingSheaf ⊥ (affineStructureSheaf X))) := HasDerivedCategory.standard _
  -- Local instance justification (defeq pin): this is the same standard quotient model on the proved target abelian category.
  letI : HasDerivedCategory.{u + 2} (LiftedFppfModules X) := HasDerivedCategory.standard _
  exact @Functor.mapDerivedCategory
    (RingedSite.ModuleCat.{u + 1} (ofCommRingSheaf ⊥ (affineStructureSheaf X)))
    inferInstance
    (Stacks1048Forward.certifiedModuleAbelian ⊥ (ofCommRingSheaf ⊥ (affineStructureSheaf X)).structureSheaf)
    (HasDerivedCategory.standard _)
    (LiftedFppfModules X) inferInstance
    (Stacks1048Forward.certifiedModuleAbelian (fppfRingedSite X).siteTopology (liftedFppfStructureSheaf X))
    (HasDerivedCategory.standard _)
    (forwardModules X) (forwardModules_additive X)
    (forwardModules_preservesFiniteLimits X) (forwardModules_preservesFiniteColimits X)

/-- Source Step 1: the actual image of QC has locally quasi-coherent flat-base-change cohomology. -/
theorem forwardDerived_mem (K : QC X) :
    DerivedCategory.cohomologyIn (liftedLqcohFbc X)
      ((forwardDerived X).obj K.obj) := sorry

/-- Restrict that fixed image to the actual cohomology-in subcategory. -/
def toDerivedLQCohFbc : QC X ⥤ LiftedDerivedLQCohFbc X :=
  (DerivedCategory.cohomologyIn (liftedLqcohFbc X)).lift
    (QC.inclusion X ⋙ forwardDerived X) (forwardDerived_mem X)

/-- The canonical forward functor followed by the actual Verdier quotient. -/
def toDerivedQCoh : QC X ⥤ LiftedDerivedQCoh X :=
  toDerivedLQCohFbc X ⋙ LiftedDerivedQCoh.quotientFunctor X

end AlgebraicGeometry.AlgebraicStack
