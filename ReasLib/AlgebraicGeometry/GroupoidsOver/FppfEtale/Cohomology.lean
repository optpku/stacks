/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.FppfEtale.Modules
public import ReasLib.AlgebraicGeometry.GroupoidsOver.HigherDirectImage
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Absolute
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import Mathlib.CategoryTheory.IsomorphismClasses

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.FppfEtale

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
variable (F : etaleModules X) [IsLocallyQuasiCoherent F]
variable (h_comparison : HasFlatLfpModuleComparison F)

/-- Derived restriction to the étale topology of a locally quasi-coherent module with
flat locally finitely presented comparisons is its ordinary restriction in degree zero. -/
theorem pushforward_single :
    IsIsomorphic
      ((epsilonPushforwardDerived X).obj
        (RingedSite.Module.singleDerived.{u + 1} (ringedSite X)
          (RingedSite.Module.carrierLift (ringedSite X)
            (toFppfModule F (isSheaf_fppf_of_isLocallyQuasiCoherent F h_comparison)))))
      (RingedSite.Module.singleDerived.{u + 1} (etaleRingedSite X)
        ((etaleFppfHom X).modulePushforward.{u + 1}.obj
          (RingedSite.Module.carrierLift (ringedSite X)
            (toFppfModule F (isSheaf_fppf_of_isLocallyQuasiCoherent F h_comparison))))) := sorry

/-- Derived global sections agree in the fppf and étale topologies for locally quasi-coherent
modules with invertible flat locally finitely presented comparisons. -/
theorem derivedGlobalSections :
    IsIsomorphic
      ((RingedSite.Hom.moduleGlobalSectionsDerived.{u + 1} (ringedSite X)).obj
        (RingedSite.Module.singleDerived.{u + 1} (ringedSite X)
          (RingedSite.Module.carrierLift (ringedSite X)
            (toFppfModule F (isSheaf_fppf_of_isLocallyQuasiCoherent F h_comparison)))))
      ((RingedSite.Hom.moduleGlobalSectionsDerived.{u + 1} (etaleRingedSite X)).obj
        (RingedSite.Module.singleDerived.{u + 1} (etaleRingedSite X)
          (RingedSite.Module.carrierLift (etaleRingedSite X) F))) := sorry

/-- Derived sections over every object agree in the fppf and étale topologies for locally
quasi-coherent modules with invertible flat locally finitely presented comparisons. -/
theorem derivedSections (x : X.total) :
    IsIsomorphic
      ((RingedSite.Hom.moduleSectionsDerived.{u + 1} (ringedSite X) x).obj
        (RingedSite.Module.singleDerived.{u + 1} (ringedSite X)
          (RingedSite.Module.carrierLift (ringedSite X)
            (toFppfModule F (isSheaf_fppf_of_isLocallyQuasiCoherent F h_comparison)))))
      ((RingedSite.Hom.moduleSectionsDerived.{u + 1} (etaleRingedSite X) x).obj
        (RingedSite.Module.singleDerived.{u + 1} (etaleRingedSite X)
          (RingedSite.Module.carrierLift (etaleRingedSite X) F))) := sorry

/-- Global cohomology agrees in every nonnegative degree between the fppf and étale topologies
for locally quasi-coherent modules with invertible flat locally finitely presented comparisons. -/
theorem cohomology (p : ℕ) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (p : ℤ)).obj
        ((RingedSite.Hom.moduleGlobalSectionsDerived.{u + 1} (ringedSite X)).obj
          (RingedSite.Module.singleDerived.{u + 1} (ringedSite X)
            (RingedSite.Module.carrierLift (ringedSite X)
              (toFppfModule F (isSheaf_fppf_of_isLocallyQuasiCoherent F h_comparison))))))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (p : ℤ)).obj
        ((RingedSite.Hom.moduleGlobalSectionsDerived.{u + 1} (etaleRingedSite X)).obj
          (RingedSite.Module.singleDerived.{u + 1} (etaleRingedSite X)
            (RingedSite.Module.carrierLift (etaleRingedSite X) F)))) := sorry

/-- Objectwise cohomology groups agree in every nonnegative degree between the fppf and étale
topologies for locally quasi-coherent modules with flat locally finitely presented comparisons. -/
theorem cohomologyAt (p : ℕ) (x : X.total) :
    IsIsomorphic
      ((forget₂ (ModuleCat.{u + 1} ((ringedSite X).structureSheaf.obj.obj (op x)))
          AddCommGrpCat.{u + 1}).obj
        ((DerivedCategory.homologyFunctor
            (ModuleCat.{u + 1} ((ringedSite X).structureSheaf.obj.obj (op x))) (p : ℤ)).obj
          ((RingedSite.Hom.moduleSectionsDerived.{u + 1} (ringedSite X) x).obj
            (RingedSite.Module.singleDerived.{u + 1} (ringedSite X)
              (RingedSite.Module.carrierLift (ringedSite X)
                (toFppfModule F (isSheaf_fppf_of_isLocallyQuasiCoherent F h_comparison)))))))
      ((forget₂ (ModuleCat.{u + 1} ((etaleRingedSite X).structureSheaf.obj.obj (op x)))
          AddCommGrpCat.{u + 1}).obj
        ((DerivedCategory.homologyFunctor
            (ModuleCat.{u + 1} ((etaleRingedSite X).structureSheaf.obj.obj (op x))) (p : ℤ)).obj
          ((RingedSite.Hom.moduleSectionsDerived.{u + 1} (etaleRingedSite X) x).obj
            (RingedSite.Module.singleDerived.{u + 1} (etaleRingedSite X)
              (RingedSite.Module.carrierLift (etaleRingedSite X) F))))) := sorry

/-- Higher fppf direct images of locally quasi-coherent modules with flat locally finitely
presented comparisons are the fppf sheafifications of their étale higher direct images. -/
theorem higherDirectImage {Y : GroupoidsOver S} (f : X ⟶ Y) (i : ℕ) :
    IsIsomorphic
      (GroupoidsOver.higherDirectImage f .fppf
        (fppfAbelianSheaf F (isSheaf_fppf_of_isLocallyQuasiCoherent F h_comparison)) i)
      ((GrothendieckTopology.TopologyComparison.pullback AddCommGrpCat.{u + 1}
          (etaleTopology_le_fppfTopology Y)).obj
        (GroupoidsOver.higherDirectImage f .etale (etaleAbelianSheaf F) i)) := sorry

/-- Derived fppf inverse image agrees with derived étale inverse image followed by derived
topology-change pullback for locally quasi-coherent modules with flat lfp comparisons. -/
theorem derivedPullback {Z : GroupoidsOver S} (g : Z ⟶ X) :
    IsIsomorphic
      ((fppfInverseImageDerived g).obj
        (RingedSite.Module.singleDerived.{u + 1} (ringedSite X)
          (RingedSite.Module.carrierLift (ringedSite X)
            (toFppfModule F (isSheaf_fppf_of_isLocallyQuasiCoherent F h_comparison)))))
      ((epsilonPullbackDerived Z).obj
        ((etaleInverseImageDerived g).obj
          (RingedSite.Module.singleDerived.{u + 1} (etaleRingedSite X)
            (RingedSite.Module.carrierLift (etaleRingedSite X) F)))) := sorry

end AlgebraicGeometry.GroupoidsOver.FppfEtale
