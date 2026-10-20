/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AtlasModuleComparison

/-! # Quasi-coherent comparison on algebraic-space sites -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.AssociatedModule
open AlgebraicGeometry.AlgebraicSpace.Etale
open AlgebraicGeometry.AlgebraicSpace.Fppf
open RingedSite.Hom

noncomputable section

universe u

/- Lemma 84.7.1 (1): The geometric sections rule satisfies fpqc descent. -/
@[stacks 0DGN] #check (AlgebraicGeometry.AlgebraicSpace.AssociatedModule.associatedPresheaf_isSheaf_fpqc :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent],
    Presheaf.IsSheaf (overFpqcTopology X) (associatedPresheaf F))

/- Lemma 84.7.1 (1): The geometric sections rule satisfies fppf descent. -/
@[stacks 0DGN] #check (AlgebraicGeometry.AlgebraicSpace.AssociatedModule.associatedPresheaf_isSheaf_fppf :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent],
    Presheaf.IsSheaf (overFppfTopology X) (associatedPresheaf F))

/- Lemma 84.7.1 (1): The geometric sections rule satisfies étale descent. -/
@[stacks 0DGN] #check (AlgebraicGeometry.AlgebraicSpace.AssociatedModule.associatedPresheaf_isSheaf_etale :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent],
    Presheaf.IsSheaf (overEtaleTopology X) (associatedPresheaf F))

/- Lemma 84.7.1 (2): The sections rule agrees with pullback along π_X. -/
@[stacks 0DGN] #check (AlgebraicGeometry.AlgebraicSpace.AssociatedModule.piPullbackIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent]
    [(Etale.Atlas.etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint],
    IsIsomorphic (piPullbackAb F) (associatedPresheaf F))

/- Lemma 84.7.1 (3): The sections rule agrees with pullback along a_X. -/
@[stacks 0DGN] #check (AlgebraicGeometry.AlgebraicSpace.AssociatedModule.aPullbackIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent]
    [(aRingedHom X).modulePushforward.{u}.IsRightAdjoint],
    IsIsomorphic (aPullbackAb F) (associatedPresheaf F))

/- Lemma 84.7.1 (4): Pullback induces an equivalence of quasi-coherent module categories on the big étale site. -/
@[stacks 0DGN] #check (AlgebraicGeometry.AlgebraicSpace.AssociatedModule.associatedFunctor_etale_isEquivalence :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [(Etale.Atlas.etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint],
    (associatedFunctor_etale X).IsEquivalence)

/- Lemma 84.7.1 (5): Pullback induces an equivalence of quasi-coherent module categories on the big fppf site. -/
@[stacks 0DGN] #check (AlgebraicGeometry.AlgebraicSpace.AssociatedModule.associatedFunctor_fppf_isEquivalence :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [(aRingedHom X).modulePushforward.{u}.IsRightAdjoint],
    (associatedFunctor_fppf X).IsEquivalence)

/- Lemma 84.7.1 (6): Pushforward along ε_X identifies a_X-pullback with π_X-pullback. -/
@[stacks 0DGN] #check (AlgebraicGeometry.AlgebraicSpace.AssociatedModule.epsilon_pushforward_aPullbackIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent]
    [(Etale.Atlas.etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint]
    [(aRingedHom X).modulePushforward.{u}.IsRightAdjoint],
    IsIsomorphic
      ((epsilonRingedHom X).modulePushforward.{u}.obj
        ((aRingedHom X).modulePullback.{u}.obj F))
      ((Etale.Atlas.etalePiRingedHom X).modulePullback.{u}.obj F))

/- Lemma 84.7.1 (6): Pushforward along a_X recovers the original module. -/
@[stacks 0DGN] #check (AlgebraicGeometry.AlgebraicSpace.AssociatedModule.a_pushforward_aPullbackIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent]
    [(aRingedHom X).modulePushforward.{u}.IsRightAdjoint],
    IsIsomorphic
      ((aRingedHom X).modulePushforward.{u}.obj
        ((aRingedHom X).modulePullback.{u}.obj F))
      F)

/- Lemma 84.7.1 (7): Positive higher direct images along ε_X vanish. -/
@[stacks 0DGN] #check (AlgebraicGeometry.AlgebraicSpace.AssociatedModule.epsilon_higherDirectImage_vanishes :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent]
    [(aRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [HasInjectiveResolutions (RingedSite.ModuleCat.{u + 1} (overFppfRingedSite X))],
    ∀ i : ℕ, 0 < i →
      IsZero
        (higherDirectImageModule (epsilonRingedHom X)
          ((aRingedHom X).modulePullback.{u + 1}.obj
            (RingedSite.Module.carrierLift (ringedSite X) F))
          i))

/- Lemma 84.7.1 (7): Positive higher direct images along a_X vanish. -/
@[stacks 0DGN] #check (AlgebraicGeometry.AlgebraicSpace.AssociatedModule.a_higherDirectImage_vanishes :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent]
    [(aRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [HasInjectiveResolutions (RingedSite.ModuleCat.{u + 1} (overFppfRingedSite X))],
    ∀ i : ℕ, 0 < i →
      IsZero
        (higherDirectImageModule (aRingedHom X)
          ((aRingedHom X).modulePullback.{u + 1}.obj
            (RingedSite.Module.carrierLift (ringedSite X) F))
          i))

end

end
