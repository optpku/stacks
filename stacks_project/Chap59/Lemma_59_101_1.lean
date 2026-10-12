/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.EtaleComparison

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.StandardTopology
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Etale.ModuleComparison
open AlgebraicGeometry.Scheme.Etale.Small

universe u

noncomputable section

/- Lemma 59.101.1 (1): the geometric pullback-sections rule is an fppf sheaf. -/
@[stacks 0DEW] #check
  (AlgebraicGeometry.Scheme.Etale.ModuleComparison.etalePullbackSections_isSheaf .fppf :
    ∀ (S : Scheme.{u})
      (F : RingedSite.ModuleCat.{u} (Small.ringedSite S)) [F.IsQuasicoherent],
      Presheaf.IsSheaf (StandardTopology.fppf.overTopology S)
        (ModuleComparison.GeometricSections.presheaf S F))

/- Lemma 59.101.1 (2): the geometric pullback-sections rule is an etale sheaf. -/
@[stacks 0DEW] #check
  (AlgebraicGeometry.Scheme.Etale.ModuleComparison.etalePullbackSections_isSheaf .etale :
    ∀ (S : Scheme.{u})
      (F : RingedSite.ModuleCat.{u} (Small.ringedSite S)) [F.IsQuasicoherent],
      Presheaf.IsSheaf (StandardTopology.etale.overTopology S)
        (ModuleComparison.GeometricSections.presheaf S F))

/- Lemma 59.101.1 (3): the extension of a quasi-coherent small-étale module is isomorphic to its big étale pullback. -/
@[stacks 0DEW] #check
  (AlgebraicGeometry.Scheme.Etale.ModuleComparison.bigEtale_associatedModule_piIso :
    ∀ (S : Scheme.{u}) (F : RingedSite.ModuleCat.{u} (Small.ringedSite S))
    [F.IsQuasicoherent],
    IsIsomorphic
      (ModuleComparison.etaleModuleExtension .etale S F)
      ((SiteRestriction.bigToEtale .etale S
          (fun h ↦ nomatch h)).modulePullback.{u}.obj
        F))

/- Lemma 59.101.1 (4): the extension of a quasi-coherent small-étale module is isomorphic to its big fppf pullback. -/
@[stacks 0DEW] #check
  (AlgebraicGeometry.Scheme.Etale.ModuleComparison.bigFppf_associatedModule_aIso :
    ∀ (S : Scheme.{u}) (F : RingedSite.ModuleCat.{u} (Small.ringedSite S))
    [F.IsQuasicoherent],
    IsIsomorphic
      (ModuleComparison.etaleModuleExtension .fppf S F)
      ((SiteRestriction.bigToEtale .fppf S
          (fun h ↦ nomatch h)).modulePullback.{u}.obj
        F))

/- Lemma 59.101.1 (5): extension to the big etale site is an equivalence. -/
@[stacks 0DEW] #check
  (AlgebraicGeometry.Scheme.Etale.ModuleComparison.etaleModuleExtensionFunctor_isEquivalence .etale :
    ∀ (S : Scheme.{u}),
      (etaleModuleExtensionFunctor .etale S).IsEquivalence)

/- Lemma 59.101.1 (6): extension to the big fppf site is an equivalence. -/
@[stacks 0DEW] #check
  (AlgebraicGeometry.Scheme.Etale.ModuleComparison.etaleModuleExtensionFunctor_isEquivalence .fppf :
    ∀ (S : Scheme.{u}),
      (etaleModuleExtensionFunctor .fppf S).IsEquivalence)

/- Lemma 59.101.1 (7): the big fppf pullback pushed forward to the big étale site is isomorphic to the big étale pullback. -/
@[stacks 0DEW] #check
  (AlgebraicGeometry.Scheme.Etale.ModuleComparison.epsilon_pushforward_aPullbackIso :
    ∀ (S : Scheme.{u}) (F : RingedSite.ModuleCat.{u} (Small.ringedSite S))
    [F.IsQuasicoherent],
    IsIsomorphic
      ((Big.toFppfHom .etale S).modulePushforward.obj
        ((SiteRestriction.bigToEtale .fppf S
          (fun h ↦ nomatch h)).modulePullback.{u}.obj
          F))
      ((SiteRestriction.bigToEtale .etale S
          (fun h ↦ nomatch h)).modulePullback.{u}.obj
        F))

/- Lemma 59.101.1 (8): the big fppf pullback pushed forward to the small étale site is isomorphic to the original quasi-coherent module. -/
@[stacks 0DEW] #check
  (AlgebraicGeometry.Scheme.Etale.ModuleComparison.a_pushforward_aPullbackIso :
    ∀ (S : Scheme.{u}) (F : RingedSite.ModuleCat.{u} (Small.ringedSite S))
    [F.IsQuasicoherent],
    IsIsomorphic
      ((SiteRestriction.bigToEtale .fppf S
          (fun h ↦ nomatch h)).modulePushforward.obj
        ((SiteRestriction.bigToEtale .fppf S
            (fun h ↦ nomatch h)).modulePullback.{u}.obj
          F))
      F)

/- Lemma 59.101.1 (9): positive higher direct images from the big fppf site to the big étale site vanish on the pullback of a quasi-coherent small-étale module. -/
@[stacks 0DEW] #check
  (AlgebraicGeometry.Scheme.Etale.ModuleComparison.epsilon_higherDirectImage_vanishes :
    ∀ (S : Scheme.{u}) (F : RingedSite.ModuleCat.{u} (Small.ringedSite S))
    [F.IsQuasicoherent],
    ∀ i : ℕ, 0 < i →
      IsZero
        (RingedSite.Hom.higherDirectImageModule
          (Big.toFppfHom .etale S)
          ((SiteRestriction.bigToEtale .fppf S
            (fun h ↦ nomatch h)).modulePullback.{u + 1}.obj
            (RingedSite.Module.carrierLift (Small.ringedSite S) F))
          i))

/- Lemma 59.101.1 (10): positive higher direct images from the big fppf site to the small étale site vanish on the pullback of a quasi-coherent small-étale module. -/
@[stacks 0DEW] #check
  (AlgebraicGeometry.Scheme.Etale.ModuleComparison.a_higherDirectImage_vanishes :
    ∀ (S : Scheme.{u}) (F : RingedSite.ModuleCat.{u} (Small.ringedSite S))
    [F.IsQuasicoherent],
    ∀ i : ℕ, 0 < i →
      IsZero
        (RingedSite.Hom.higherDirectImageModule
          (SiteRestriction.bigToEtale .fppf S
            (fun h ↦ nomatch h))
          ((SiteRestriction.bigToEtale .fppf S
              (fun h ↦ nomatch h)).modulePullback.{u + 1}.obj
            (RingedSite.Module.carrierLift (Small.ringedSite S) F))
          i))
