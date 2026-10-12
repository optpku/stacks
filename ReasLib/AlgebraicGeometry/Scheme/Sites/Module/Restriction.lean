/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.PullbackSections

/-!
# Pullback of modules along restriction morphisms of scheme sites

The restriction morphisms from standard big and small étale sites to the small Zariski
site form commutative squares with the corresponding morphisms induced by a scheme map.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.StandardTopology.Big

/-- Module pushforward along a morphism of standard big ringed sites has its canonical
inverse-image left adjoint. -/
noncomputable instance ringedHom_modulePushforward_isRightAdjoint
    (τX τY : StandardTopology) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsMorphismOfSites (τY.overTopology Y) (τX.overTopology X) (Over.pullback f)] :
    ((ringedHom τX τY f).modulePushforward.{u}).IsRightAdjoint := sorry

end AlgebraicGeometry.StandardTopology.Big

namespace AlgebraicGeometry.Scheme.SiteRestriction

/-- For a scheme module, restriction from its small Zariski source view to a standard
big site is the canonical inverse-image/sheafification isomorphism. -/
noncomputable def bigZariskiIso_sourceView
    (τ : StandardTopology) (S : Scheme.{u}) (F : S.Modules) :
    (bigToZariski τ S).modulePullback.obj (sourceSmallZariskiView S F) ≅
      (_root_.PresheafOfModules.sheafification
        (𝟙 (StandardTopology.Big.structureSheaf τ S).obj)).obj
          (bigZariskiPullbackSections τ S (sourceSmallZariskiView S F)) :=
  bigZariskiIso τ S (sourceSmallZariskiView S F)

/-- For a scheme module, restriction from its small Zariski source view to the small
étale site is the canonical inverse-image/sheafification isomorphism. -/
noncomputable def smallEtaleZariskiIso_sourceView
    (S : Scheme.{u}) (F : S.Modules) :
    (smallEtaleToZariski S).modulePullback.obj (sourceSmallZariskiView S F) ≅
      (_root_.PresheafOfModules.sheafification
        (𝟙 (Scheme.Etale.Small.structureSheaf S).obj)).obj
          (smallEtaleZariskiPullbackSections S (sourceSmallZariskiView S F)) :=
  smallEtaleZariskiIso S (sourceSmallZariskiView S F)

/-- The square relating small-Zariski pullback and standard-big pullback commutes. -/
theorem bigNaturality
    (τX τY : StandardTopology) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsMorphismOfSites (τY.overTopology Y) (τX.overTopology X) (Over.pullback f)] :
    RingedSite.Hom.comp (bigToZariski τX X) (Scheme.Zariski.Small.ringedHom f) =
      RingedSite.Hom.comp (StandardTopology.Big.ringedHom τX τY f)
        (bigToZariski τY Y) := sorry

/-- The canonical natural isomorphism comparing associated-module pullback on a standard
big site with pullback on the small Zariski site. -/
noncomputable def bigNaturalityIso
    (τX τY : StandardTopology) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsMorphismOfSites (τY.overTopology Y) (τX.overTopology X) (Over.pullback f)] :
    (Scheme.Zariski.Small.ringedHom f).modulePullback.{u} ⋙
        (bigToZariski τX X).modulePullback.{u} ≅
      (bigToZariski τY Y).modulePullback.{u} ⋙
        (StandardTopology.Big.ringedHom τX τY f).modulePullback.{u} :=
  RingedSite.Hom.CommSq.pullbackIso (bigNaturality τX τY f)

/-- `bigNaturalityIso` is the generic pullback comparison for the standard-big
restriction square. -/
theorem bigNaturalityIso_def
    (τX τY : StandardTopology) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsMorphismOfSites (τY.overTopology Y) (τX.overTopology X) (Over.pullback f)] :
    bigNaturalityIso τX τY f =
      RingedSite.Hom.CommSq.pullbackIso (bigNaturality τX τY f) := sorry

/-- For a scheme module, the standard-big pullback comparison evaluated on its small
Zariski source view. -/
noncomputable def bigNaturalityIso_sourceView
    (τX τY : StandardTopology) (X Y : Scheme.{u}) (f : X ⟶ Y) (F : Y.Modules)
    [IsMorphismOfSites (τY.overTopology Y) (τX.overTopology X) (Over.pullback f)] :
    ((Scheme.Zariski.Small.ringedHom f).modulePullback ⋙
        (bigToZariski τX X).modulePullback).obj (sourceSmallZariskiView Y F) ≅
      ((bigToZariski τY Y).modulePullback ⋙
        (StandardTopology.Big.ringedHom τX τY f).modulePullback).obj
          (sourceSmallZariskiView Y F) :=
  (bigNaturalityIso τX τY f).app (sourceSmallZariskiView Y F)

/-- The square relating small-Zariski pullback and small-étale pullback commutes. -/
theorem smallEtaleNaturality {X Y : Scheme.{u}} (f : X ⟶ Y) :
    RingedSite.Hom.comp (smallEtaleToZariski X) (Scheme.Zariski.Small.ringedHom f) =
      RingedSite.Hom.comp (Scheme.Etale.Small.ringedHom f)
        (smallEtaleToZariski Y) := sorry

/-- The canonical natural isomorphism comparing associated-module pullback on a small
étale site with pullback on the small Zariski site. -/
noncomputable def smallEtaleNaturalityIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Zariski.Small.ringedHom f).modulePullback.{u} ⋙
        (smallEtaleToZariski X).modulePullback.{u} ≅
      (smallEtaleToZariski Y).modulePullback.{u} ⋙
        (Scheme.Etale.Small.ringedHom f).modulePullback.{u} :=
  RingedSite.Hom.CommSq.pullbackIso (smallEtaleNaturality f)

/-- `smallEtaleNaturalityIso` is the generic pullback comparison for the small-étale
restriction square. -/
theorem smallEtaleNaturalityIso_def {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleNaturalityIso f =
      RingedSite.Hom.CommSq.pullbackIso (smallEtaleNaturality f) := sorry

/-- For a scheme module, the small-étale pullback comparison evaluated on its small
Zariski source view. -/
noncomputable def smallEtaleNaturalityIso_sourceView
    (X Y : Scheme.{u}) (f : X ⟶ Y) (F : Y.Modules) :
    ((Scheme.Zariski.Small.ringedHom f).modulePullback ⋙
        (smallEtaleToZariski X).modulePullback).obj (sourceSmallZariskiView Y F) ≅
      ((smallEtaleToZariski Y).modulePullback ⋙
        (Scheme.Etale.Small.ringedHom f).modulePullback).obj
          (sourceSmallZariskiView Y F) :=
  (smallEtaleNaturalityIso f).app (sourceSmallZariskiView Y F)

end AlgebraicGeometry.Scheme.SiteRestriction
