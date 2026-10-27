/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.SiteSized
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.QuasiCoherent.Lifted
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.ObjectProperty.Shift

/-!
# The canonical comparison for derived quasi-coherent objects on an algebraic stack

Module sheafification on the chaotic affine site is followed by extension from
the affine basis and sheafification on the fppf site. The exact derived functor
lands in locally quasi-coherent flat-base-change cohomology and then in the
Verdier quotient by parasitic cohomology.
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
    PresheafOfModules.SiteSized.sheafification (affineSiteFppfTopology X)
      (affineFppfRestrictedStructureSheaf X)

/-- Extension from affine objects uses the actual presheaf pullback and sheafification.
The pullback certificate is the proved free-generator construction on AsSmall. -/
def affineExtensionModules :
    RingedSite.ModuleCat.{u + 1} (affineFppfRingedSite X) ⥤ LiftedFppfModules X :=
  SheafOfModules.forget (affineFppfRestrictedStructureSheaf X) ⋙
    PresheafOfModules.SiteSized.pullback (F := affineInclusion X)
      (R := (liftedFppfStructureSheaf X).obj) (𝟙 _) ⋙
    PresheafOfModules.SiteSized.sheafification (ringedSite X).siteTopology
      (liftedFppfStructureSheaf X)

/-- The underived forward functor is the specified epsilon/affine composite. -/
def forwardModules := epsilonModules X ⋙ affineExtensionModules X

/-- These fixed underived sheafification/affine-basis functors are additive. -/
instance forwardModules_additive : (forwardModules X).Additive := sorry

/-- Sheafification is left exact and dense-affine extension is an exact equivalence. -/
instance forwardModules_preservesFiniteLimits : PreservesFiniteLimits (forwardModules X) := sorry

/-- Both specified left adjoints preserve finite colimits. -/
instance forwardModules_preservesFiniteColimits : PreservesFiniteColimits (forwardModules X) := sorry

/-- The derived forward functor obtained by applying the exact module comparison
degreewise and localizing at quasi-isomorphisms. -/
def forwardDerived :
    Hom.ModuleDerived.{u + 1} (ofCommRingSheaf ⊥ (affineStructureSheaf X)) ⥤
      LiftedModuleDerived X := by
  -- Local instance justification (instance diamond): use the proved module-sheaf abelian structure on the source, including its finite constructions.
  letI : Abelian (RingedSite.ModuleCat.{u + 1}
      (ofCommRingSheaf ⊥ (affineStructureSheaf X))) :=
    SheafOfModules.SiteSized.abelian ⊥
      (ofCommRingSheaf ⊥ (affineStructureSheaf X)).structureSheaf
  -- Local instance justification (instance diamond): use the proved abelian structure on the target instead of the imported admitted presentation bridge.
  letI : Abelian (LiftedFppfModules X) :=
    SheafOfModules.SiteSized.abelian (ringedSite X).siteTopology
      (liftedFppfStructureSheaf X)
  -- Local instance justification (defeq pin): this is the standard quotient model of the actual source cochain category.
  letI : HasDerivedCategory.{u + 2} (RingedSite.ModuleCat.{u + 1}
      (ofCommRingSheaf ⊥ (affineStructureSheaf X))) := HasDerivedCategory.standard _
  -- Local instance justification (defeq pin): this is the same standard quotient model on the proved target abelian category.
  letI : HasDerivedCategory.{u + 2} (LiftedFppfModules X) := HasDerivedCategory.standard _
  exact @Functor.mapDerivedCategory
    (RingedSite.ModuleCat.{u + 1} (ofCommRingSheaf ⊥ (affineStructureSheaf X))) inferInstance
    (SheafOfModules.SiteSized.abelian ⊥
      (ofCommRingSheaf ⊥ (affineStructureSheaf X)).structureSheaf) (HasDerivedCategory.standard _)
    (LiftedFppfModules X) inferInstance
    (SheafOfModules.SiteSized.abelian (ringedSite X).siteTopology
      (liftedFppfStructureSheaf X)) (HasDerivedCategory.standard _)
    (forwardModules X) (forwardModules_additive X)
    (forwardModules_preservesFiniteLimits X) (forwardModules_preservesFiniteColimits X)

/-- The image of a quasi-coherent derived object has locally quasi-coherent
flat-base-change cohomology. -/
theorem forwardDerived_mem (K : QC X) :
    DerivedCategory.cohomologyIn (liftedLqcohFbc X)
      ((forwardDerived X).obj K.obj) := sorry

/-- The forward functor with codomain restricted to locally quasi-coherent
flat-base-change cohomology. -/
def toDerivedLQCohFbc : QC X ⥤ LiftedDerivedLQCohFbc X :=
  (DerivedCategory.cohomologyIn (liftedLqcohFbc X)).lift
    (QC.inclusion X ⋙ forwardDerived X) (forwardDerived_mem X)

/-- The canonical forward functor followed by the actual Verdier quotient. -/
def toDerivedQCoh : QC X ⥤ LiftedDerivedQCoh X :=
  toDerivedLQCohFbc X ⋙ LiftedDerivedQCoh.quotientFunctor X

/-- The exact-derived forward functor carries its actual standard shift maps. -/
instance forwardDerived_commShift : (forwardDerived X).CommShift ℤ := by
  -- Local instance justification (defeq pin): select the standard chaotic-module derived model already fixed in forwardDerived.
  letI := moduleCat_hasDerivedCategory.{u + 1}
    (ofCommRingSheaf ⊥ (affineStructureSheaf X))
  change (forwardModules X).mapDerivedCategory.CommShift ℤ
  infer_instance

/-- The forward functor to locally quasi-coherent flat-base-change cohomology
commutes with shifts via the restricted derived comparison maps. -/
instance toDerivedLQCohFbc_commShift : (toDerivedLQCohFbc X).CommShift ℤ := by
  unfold toDerivedLQCohFbc
  infer_instance

/-- The canonical forward functor commutes with shifts via the derived comparison
and Verdier quotient shift maps. -/
instance toDerivedQCoh_commShift : (toDerivedQCoh X).CommShift ℤ := by
  change (toDerivedLQCohFbc X ⋙ LiftedDerivedQCoh.quotientFunctor X).CommShift ℤ
  infer_instance

/-- The specified functor preserves distinguished triangles. -/
instance toDerivedQCoh_isTriangulated : (toDerivedQCoh X).IsTriangulated := sorry

/-- The specified functor is integer-linear. -/
instance toDerivedQCoh_linear : (toDerivedQCoh X).Linear ℤ := sorry

/-- The canonical forward functor from quasi-coherent derived objects on the
chaotic affine site to the parasitic Verdier quotient is an equivalence. -/
theorem toDerivedQCoh_isEquivalence {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : (toDerivedQCoh X).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicStack
