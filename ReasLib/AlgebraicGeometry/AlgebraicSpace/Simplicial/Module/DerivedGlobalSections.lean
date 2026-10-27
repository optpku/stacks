/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.NativeGlobalSections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SpacesGrothendieck
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.QCoh.DerivedDescent

@[expose] public section

open CategoryTheory
open Functor
open RingedSite.ToposHom.NativeDerived
open scoped Simplicial

noncomputable section

set_option backward.privateInPublic true

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Derived direct image along the total étale augmentation preserves derived global sections. -/
private def augmentationLerayIso :
    QCohDerived.ambientPushforward a ⋙ derivedGlobalSections (spacesRingedSite X) ≅
      derivedGlobalSections (etaleTotalRingedSite U) := by
  -- Local instance justification (defeq pin): the Leray comparison uses the actual total-derived direct image certified by the native K-injective construction.
  letI := EtaleModuleDerived.hasPushforward a
  exact rGammaPushforwardIso (spacesEtaleAugmentationRinged U a)

/-- The derived augmentation unit followed by Leray gives the canonical pullback comparison on global sections. -/
def rGammaPullbackComparison (ha : IsFppfHypercovering a) :
    derivedGlobalSections (spacesRingedSite X) ⟶
      QCohDerived.ambientPullback a ha ⋙ derivedGlobalSections (etaleTotalRingedSite U) :=
  whiskerRight (QCohDerived.ambientAdjunction a ha).unit
      (derivedGlobalSections (spacesRingedSite X)) ≫
    (associator (QCohDerived.ambientPullback a ha) (QCohDerived.ambientPushforward a)
      (derivedGlobalSections (spacesRingedSite X))).hom ≫
    whiskerLeft (QCohDerived.ambientPullback a ha) (augmentationLerayIso a).hom

/-- At a derived module, the pullback comparison is the mapped adjunction unit followed by the Leray component. -/
theorem rGammaPullbackComparison_app (ha : IsFppfHypercovering a)
    (K : RingedSite.NativeDerived.category.{u} (spacesRingedSite X)) :
    (rGammaPullbackComparison a ha).app K =
      (derivedGlobalSections (spacesRingedSite X)).map
        ((QCohDerived.ambientAdjunction a ha).unit.app K) ≫
      (augmentationLerayIso a).hom.app ((QCohDerived.ambientPullback a ha).obj K) := sorry

/-- An fppf hypercovering preserves derived global sections of every unbounded complex with quasi-coherent homology. -/
theorem rGammaPullbackComparison_app_isIso (ha : IsFppfHypercovering a)
    (K : QCohDerived.Base X) :
    IsIso ((rGammaPullbackComparison a ha).app K.obj) := sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial
