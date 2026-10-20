/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Proposition 35.9.4 (1): associated quasi-coherent modules on every standard
big site commute with pullback along a scheme morphism. -/
@[stacks 03LC] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.pullbackCompatibleBig :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}}
      (τ : AlgebraicGeometry.StandardTopology) (f : T ⟶ S),
      IsIsomorphic
        (AlgebraicGeometry.Scheme.AssociatedModule.bigFunctor τ S ⋙
          AlgebraicGeometry.StandardTopology.Big.QCoh.pullback τ f)
        (AlgebraicGeometry.Scheme.QCoh.pullback f ⋙
          AlgebraicGeometry.Scheme.AssociatedModule.bigFunctor τ T))

/- Proposition 35.9.4 (1): associated quasi-coherent modules on the small
Zariski or étale site commute with pullback along a scheme morphism. -/
@[stacks 03LC] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.pullbackCompatibleSmall :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}}
      (σ : AlgebraicGeometry.SmallStandardTopology) (f : T ⟶ S),
      IsIsomorphic
        (AlgebraicGeometry.Scheme.AssociatedModule.smallFunctor σ S ⋙
          AlgebraicGeometry.SmallStandardTopology.QCoh.pullback σ f)
        (AlgebraicGeometry.Scheme.QCoh.pullback f ⋙
          AlgebraicGeometry.Scheme.AssociatedModule.smallFunctor σ T))

/- Objectwise big-site pullback compatibility. -/
#check
  (AlgebraicGeometry.Scheme.AssociatedModule.pullbackCompatibleBigObj :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}}
      (τ : AlgebraicGeometry.StandardTopology) (f : T ⟶ S)
      (G : AlgebraicGeometry.Scheme.QCoh S),
      IsIsomorphic
        ((AlgebraicGeometry.StandardTopology.Big.QCoh.pullback τ f).obj
          ((AlgebraicGeometry.Scheme.AssociatedModule.bigFunctor τ S).obj G))
        ((AlgebraicGeometry.Scheme.AssociatedModule.bigFunctor τ T).obj
          ((AlgebraicGeometry.Scheme.QCoh.pullback f).obj G)))

/- Objectwise small-site pullback compatibility. -/
#check
  (AlgebraicGeometry.Scheme.AssociatedModule.pullbackCompatibleSmallObj :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}}
      (σ : AlgebraicGeometry.SmallStandardTopology) (f : T ⟶ S)
      (G : AlgebraicGeometry.Scheme.QCoh S),
      IsIsomorphic
        ((AlgebraicGeometry.SmallStandardTopology.QCoh.pullback σ f).obj
          ((AlgebraicGeometry.Scheme.AssociatedModule.smallFunctor σ S).obj G))
        ((AlgebraicGeometry.Scheme.AssociatedModule.smallFunctor σ T).obj
          ((AlgebraicGeometry.Scheme.QCoh.pullback f).obj G)))

/- Proposition 35.9.4 (2): for every standard big topology, big-site
pushforward is not universally compatible with qcqs scheme pushforward. -/
@[stacks 03LC] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.notBigPushforwardCompatible :
    ∀ τ : AlgebraicGeometry.StandardTopology,
      ¬ ∀ (S T : AlgebraicGeometry.Scheme.{u}) (f : T ⟶ S)
        [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f],
        IsIsomorphic
          (AlgebraicGeometry.Scheme.AssociatedModule.bigFunctor τ T ⋙
            (SheafOfModules.isQuasicoherent
              (AlgebraicGeometry.Scheme.AssociatedModule.bigStructureSheaf τ T)).ι ⋙
            (AlgebraicGeometry.StandardTopology.Big.pullbackRingedHom τ f).modulePushforward)
          (AlgebraicGeometry.Scheme.QCoh.pushforward f ⋙
            AlgebraicGeometry.Scheme.AssociatedModule.bigFunctor τ S ⋙
            (SheafOfModules.isQuasicoherent
              (AlgebraicGeometry.Scheme.AssociatedModule.bigStructureSheaf τ S)).ι))

/- Proposition 35.9.4 (3): qcqs scheme pushforward preserves quasi-coherent
modules. -/
@[stacks 03LC] #check
  (AlgebraicGeometry.Scheme.QCoh.pushforward.mapsTo :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f],
      AlgebraicGeometry.Scheme.QCoh.preservesQuasiCoherent f)

/- Proposition 35.9.4 (3): qcqs pushforward on the small Zariski or étale
site preserves quasi-coherent modules. -/
@[stacks 03LC] #check
  (AlgebraicGeometry.SmallStandardTopology.QCoh.modulePushforward_isQuasicoherent :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}}
      (σ : AlgebraicGeometry.SmallStandardTopology) (f : T ⟶ S)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
      (F : SheafOfModules
        (AlgebraicGeometry.Scheme.AssociatedModule.smallStructureSheaf σ T))
      [F.IsQuasicoherent],
      ((AlgebraicGeometry.SmallStandardTopology.QCoh.ambientPushforward σ f).obj F).IsQuasicoherent)

/- Proposition 35.9.4 (3): for a qcqs morphism, pushforward on the small
Zariski or étale site commutes with the associated-module functor. -/
@[stacks 03LC] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.smallPushforwardCompatible :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}}
      (σ : AlgebraicGeometry.SmallStandardTopology) (f : T ⟶ S)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f],
      IsIsomorphic
        (AlgebraicGeometry.Scheme.AssociatedModule.smallFunctor σ T ⋙
          AlgebraicGeometry.SmallStandardTopology.QCoh.pushforward σ f)
        (AlgebraicGeometry.Scheme.QCoh.pushforward f ⋙
          AlgebraicGeometry.Scheme.AssociatedModule.smallFunctor σ S))

/- Objectwise small-site pushforward compatibility. -/
#check
  (AlgebraicGeometry.Scheme.AssociatedModule.smallPushforwardCompatibleObj :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}}
      (σ : AlgebraicGeometry.SmallStandardTopology) (f : T ⟶ S)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
      (F : AlgebraicGeometry.Scheme.QCoh T),
      IsIsomorphic
        ((AlgebraicGeometry.SmallStandardTopology.QCoh.pushforward σ f).obj
          ((AlgebraicGeometry.Scheme.AssociatedModule.smallFunctor σ T).obj F))
        ((AlgebraicGeometry.Scheme.AssociatedModule.smallFunctor σ S).obj
          ((AlgebraicGeometry.Scheme.QCoh.pushforward f).obj F)))
