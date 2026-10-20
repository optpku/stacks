/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Restriction

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

/- Compatibility bridge for the standard-big module-pushforward adjoint instance. -/
#check
  (AlgebraicGeometry.StandardTopology.Big.ringedHom_modulePushforward_isRightAdjoint :
    ∀ (τX τY : StandardTopology) {X Y : Scheme.{u}} (f : X ⟶ Y)
        [IsMorphismOfSites
          (τY.overTopology Y) (τX.overTopology X) (Over.pullback f)],
      ((AlgebraicGeometry.StandardTopology.Big.ringedHom τX τY f).modulePushforward.{u}).IsRightAdjoint)

/- Compatibility bridge for the standard-big restriction square. -/
#check
  (AlgebraicGeometry.Scheme.SiteRestriction.bigNaturality :
    ∀ (τX τY : StandardTopology) {X Y : Scheme.{u}} (f : X ⟶ Y)
        [IsMorphismOfSites
          (τY.overTopology Y) (τX.overTopology X) (Over.pullback f)],
      RingedSite.Hom.comp
          (AlgebraicGeometry.Scheme.SiteRestriction.bigToZariski τX X)
          (AlgebraicGeometry.Scheme.Zariski.Small.ringedHom f) =
        RingedSite.Hom.comp
          (AlgebraicGeometry.StandardTopology.Big.ringedHom τX τY f)
          (AlgebraicGeometry.Scheme.SiteRestriction.bigToZariski τY Y))

/- Compatibility bridge for the standard-big module-pullback comparison. -/
#check
  (AlgebraicGeometry.Scheme.SiteRestriction.bigNaturalityIso :
    ∀ (τX τY : StandardTopology) {X Y : Scheme.{u}} (f : X ⟶ Y)
        [IsMorphismOfSites
          (τY.overTopology Y) (τX.overTopology X) (Over.pullback f)],
      (AlgebraicGeometry.Scheme.Zariski.Small.ringedHom f).modulePullback.{u} ⋙
          (AlgebraicGeometry.Scheme.SiteRestriction.bigToZariski τX X).modulePullback.{u} ≅
        (AlgebraicGeometry.Scheme.SiteRestriction.bigToZariski τY Y).modulePullback.{u} ⋙
          (AlgebraicGeometry.StandardTopology.Big.ringedHom τX τY f).modulePullback.{u})

/- Compatibility bridge for the defining equation of the standard-big comparison. -/
#check
  (AlgebraicGeometry.Scheme.SiteRestriction.bigNaturalityIso_def :
    ∀ (τX τY : StandardTopology) {X Y : Scheme.{u}} (f : X ⟶ Y)
        [IsMorphismOfSites
          (τY.overTopology Y) (τX.overTopology X) (Over.pullback f)],
      AlgebraicGeometry.Scheme.SiteRestriction.bigNaturalityIso τX τY f =
        RingedSite.Hom.CommSq.pullbackIso
          (AlgebraicGeometry.Scheme.SiteRestriction.bigNaturality τX τY f))

/- Compatibility bridge for the small-étale restriction square. -/
#check
  (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleNaturality :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      RingedSite.Hom.comp
          (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleToZariski X)
          (AlgebraicGeometry.Scheme.Zariski.Small.ringedHom f) =
        RingedSite.Hom.comp
          (AlgebraicGeometry.Scheme.Etale.Small.ringedHom f)
          (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleToZariski Y))

/- Compatibility bridge for the small-étale module-pullback comparison. -/
#check
  (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleNaturalityIso :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      (AlgebraicGeometry.Scheme.Zariski.Small.ringedHom f).modulePullback.{u} ⋙
          (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleToZariski X).modulePullback.{u} ≅
        (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleToZariski Y).modulePullback.{u} ⋙
          (AlgebraicGeometry.Scheme.Etale.Small.ringedHom f).modulePullback.{u})

/- Compatibility bridge for the defining equation of the small-étale comparison. -/
#check
  (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleNaturalityIso_def :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleNaturalityIso f =
        RingedSite.Hom.CommSq.pullbackIso
          (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleNaturality f))
