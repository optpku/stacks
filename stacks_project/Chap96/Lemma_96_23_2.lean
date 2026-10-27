/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.FppfEtale.Cohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

open FppfEtale

/- Lemma 96.23.2 (1): the module presheaf is an fppf sheaf. -/
@[stacks 075R] #check (AlgebraicGeometry.GroupoidsOver.isSheaf_fppf_of_isLocallyQuasiCoherent :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) [IsLocallyQuasiCoherent F]
    (h_comparison : ∀ {x y : X.total} (φ : x ⟶ y),
      Flat (X.p.map φ).left → LocallyOfFinitePresentation (X.p.map φ).left →
        IsIso (moduleComparison φ F)),
    Presheaf.IsSheaf X.fppfTopology F.val.presheaf)

/- Lemma 96.23.2 (2): derived restriction is ordinary restriction in degree zero. -/
@[stacks 075R] #check (AlgebraicGeometry.GroupoidsOver.FppfEtale.pushforward_single :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) [IsLocallyQuasiCoherent F]
    (h_comparison : HasFlatLfpModuleComparison F),
    IsIsomorphic
      ((epsilonPushforwardDerived X).obj
        (RingedSite.Module.singleDerived.{u + 1} (ringedSite X)
          (RingedSite.Module.carrierLift (ringedSite X)
            (toFppfModule F (isSheaf_fppf_of_isLocallyQuasiCoherent F h_comparison)))))
      (RingedSite.Module.singleDerived.{u + 1} (etaleRingedSite X)
        ((etaleFppfHom X).modulePushforward.{u + 1}.obj
          (RingedSite.Module.carrierLift (ringedSite X)
            (toFppfModule F (isSheaf_fppf_of_isLocallyQuasiCoherent F h_comparison))))))

/- Lemma 96.23.2 (3): global cohomology agrees in every nonnegative degree. -/
@[stacks 075R] #check (AlgebraicGeometry.GroupoidsOver.FppfEtale.cohomology :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) [IsLocallyQuasiCoherent F]
    (h_comparison : HasFlatLfpModuleComparison F) (p : ℕ),
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (p : ℤ)).obj
        ((RingedSite.Hom.moduleGlobalSectionsDerived.{u + 1} (ringedSite X)).obj
          (RingedSite.Module.singleDerived.{u + 1} (ringedSite X)
            (RingedSite.Module.carrierLift (ringedSite X)
              (toFppfModule F (isSheaf_fppf_of_isLocallyQuasiCoherent F h_comparison))))))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (p : ℤ)).obj
        ((RingedSite.Hom.moduleGlobalSectionsDerived.{u + 1} (etaleRingedSite X)).obj
          (RingedSite.Module.singleDerived.{u + 1} (etaleRingedSite X)
            (RingedSite.Module.carrierLift (etaleRingedSite X) F)))))

/- Lemma 96.23.2 (4): objectwise cohomology agrees in every nonnegative degree. -/
@[stacks 075R] #check (AlgebraicGeometry.GroupoidsOver.FppfEtale.cohomologyAt :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) [IsLocallyQuasiCoherent F]
    (h_comparison : HasFlatLfpModuleComparison F) (p : ℕ) (x : X.total),
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
              (RingedSite.Module.carrierLift (etaleRingedSite X) F))))))

/- Lemma 96.23.2 (5): derived global sections agree. -/
@[stacks 075R] #check (AlgebraicGeometry.GroupoidsOver.FppfEtale.derivedGlobalSections :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) [IsLocallyQuasiCoherent F]
    (h_comparison : HasFlatLfpModuleComparison F),
    IsIsomorphic
      ((RingedSite.Hom.moduleGlobalSectionsDerived.{u + 1} (ringedSite X)).obj
        (RingedSite.Module.singleDerived.{u + 1} (ringedSite X)
          (RingedSite.Module.carrierLift (ringedSite X)
            (toFppfModule F (isSheaf_fppf_of_isLocallyQuasiCoherent F h_comparison)))))
      ((RingedSite.Hom.moduleGlobalSectionsDerived.{u + 1} (etaleRingedSite X)).obj
        (RingedSite.Module.singleDerived.{u + 1} (etaleRingedSite X)
          (RingedSite.Module.carrierLift (etaleRingedSite X) F))))

/- Lemma 96.23.2 (6): derived objectwise sections agree. -/
@[stacks 075R] #check (AlgebraicGeometry.GroupoidsOver.FppfEtale.derivedSections :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) [IsLocallyQuasiCoherent F]
    (h_comparison : HasFlatLfpModuleComparison F) (x : X.total),
    IsIsomorphic
      ((RingedSite.Hom.moduleSectionsDerived.{u + 1} (ringedSite X) x).obj
        (RingedSite.Module.singleDerived.{u + 1} (ringedSite X)
          (RingedSite.Module.carrierLift (ringedSite X)
            (toFppfModule F (isSheaf_fppf_of_isLocallyQuasiCoherent F h_comparison)))))
      ((RingedSite.Hom.moduleSectionsDerived.{u + 1} (etaleRingedSite X) x).obj
        (RingedSite.Module.singleDerived.{u + 1} (etaleRingedSite X)
          (RingedSite.Module.carrierLift (etaleRingedSite X) F))))

/- Lemma 96.23.2 (7): higher direct images agree after fppf sheafification. -/
@[stacks 075R] #check (AlgebraicGeometry.GroupoidsOver.FppfEtale.higherDirectImage :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) [IsLocallyQuasiCoherent F]
    (h_comparison : HasFlatLfpModuleComparison F) {Y : GroupoidsOver S} (f : X ⟶ Y) (i : ℕ),
    IsIsomorphic
      (GroupoidsOver.higherDirectImage f .fppf
        (fppfAbelianSheaf F (isSheaf_fppf_of_isLocallyQuasiCoherent F h_comparison)) i)
      ((GrothendieckTopology.TopologyComparison.pullback AddCommGrpCat.{u + 1}
          (etaleTopology_le_fppfTopology Y)).obj
        (GroupoidsOver.higherDirectImage f .etale (etaleAbelianSheaf F) i)))

/- Lemma 96.23.2 (8): derived inverse images agree after derived topology change. -/
@[stacks 075R] #check (AlgebraicGeometry.GroupoidsOver.FppfEtale.derivedPullback :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) [IsLocallyQuasiCoherent F]
    (h_comparison : HasFlatLfpModuleComparison F) {Z : GroupoidsOver S} (g : Z ⟶ X),
    IsIsomorphic
      ((fppfInverseImageDerived g).obj
        (RingedSite.Module.singleDerived.{u + 1} (ringedSite X)
          (RingedSite.Module.carrierLift (ringedSite X)
            (toFppfModule F (isSheaf_fppf_of_isLocallyQuasiCoherent F h_comparison)))))
      ((epsilonPullbackDerived Z).obj
        ((etaleInverseImageDerived g).obj
          (RingedSite.Module.singleDerived.{u + 1} (etaleRingedSite X)
            (RingedSite.Module.carrierLift (etaleRingedSite X) F)))))

end AlgebraicGeometry.GroupoidsOver

