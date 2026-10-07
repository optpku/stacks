module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Restriction

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

/- Remark 35.8.6 (1), standard-big case: the associated module is inverse image from
the small Zariski ringed site. -/
@[stacks 03FH] #check
  (AlgebraicGeometry.Scheme.SiteRestriction.bigZariskiIso_sourceView :
    ∀ (τ : StandardTopology) (S : Scheme.{u}) (F : S.Modules),
      (AlgebraicGeometry.Scheme.SiteRestriction.bigToZariski τ S).modulePullback.obj
          (AlgebraicGeometry.Scheme.SiteRestriction.sourceSmallZariskiView S F) ≅
        (_root_.PresheafOfModules.sheafification
          (𝟙 (StandardTopology.Big.structureSheaf τ S).obj)).obj
            (AlgebraicGeometry.Scheme.SiteRestriction.bigZariskiPullbackSections τ S
              (AlgebraicGeometry.Scheme.SiteRestriction.sourceSmallZariskiView S F)))

/- Remark 35.8.6 (1), small-étale case: the associated module is inverse image from
the small Zariski ringed site. -/
@[stacks 03FH] #check
  (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleZariskiIso_sourceView :
    ∀ (S : Scheme.{u}) (F : S.Modules),
      (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleToZariski S).modulePullback.obj
          (AlgebraicGeometry.Scheme.SiteRestriction.sourceSmallZariskiView S F) ≅
        (_root_.PresheafOfModules.sheafification
          (𝟙 (AlgebraicGeometry.Scheme.Etale.Small.structureSheaf S).obj)).obj
            (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleZariskiPullbackSections S
              (AlgebraicGeometry.Scheme.SiteRestriction.sourceSmallZariskiView S F)))

/- Remark 35.8.6 (2), standard-big case: associated modules commute canonically with
pullback along a morphism between standard big sites. -/
@[stacks 03FH] #check
  (AlgebraicGeometry.Scheme.SiteRestriction.bigNaturalityIso_sourceView :
    ∀ (τX τY : StandardTopology) (X Y : Scheme.{u}) (f : X ⟶ Y) (F : Y.Modules)
        [IsMorphismOfSites
          (τY.overTopology Y) (τX.overTopology X) (Over.pullback f)],
      ((AlgebraicGeometry.Scheme.Zariski.Small.ringedHom f).modulePullback.{u} ⋙
          (AlgebraicGeometry.Scheme.SiteRestriction.bigToZariski τX X).modulePullback.{u}).obj
            (AlgebraicGeometry.Scheme.SiteRestriction.sourceSmallZariskiView Y F) ≅
        ((AlgebraicGeometry.Scheme.SiteRestriction.bigToZariski τY Y).modulePullback.{u} ⋙
          (AlgebraicGeometry.StandardTopology.Big.ringedHom τX τY f).modulePullback.{u}).obj
            (AlgebraicGeometry.Scheme.SiteRestriction.sourceSmallZariskiView Y F))

/- Remark 35.8.6 (2), small-étale case: associated modules commute canonically with
pullback along a morphism of small étale sites. -/
@[stacks 03FH] #check
  (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleNaturalityIso_sourceView :
    ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (F : Y.Modules),
      ((AlgebraicGeometry.Scheme.Zariski.Small.ringedHom f).modulePullback.{u} ⋙
          (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleToZariski X).modulePullback.{u}).obj
            (AlgebraicGeometry.Scheme.SiteRestriction.sourceSmallZariskiView Y F) ≅
        ((AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleToZariski Y).modulePullback.{u} ⋙
          (AlgebraicGeometry.Scheme.Etale.Small.ringedHom f).modulePullback.{u}).obj
            (AlgebraicGeometry.Scheme.SiteRestriction.sourceSmallZariskiView Y F))

section

variable (X Y : Scheme.{u}) (f : X ⟶ Y) (F : Y.Modules)

/- The corresponding small-Zariski pullback comparison is the reflexive isomorphism. -/
#check
  (CategoryTheory.Iso.refl
      ((AlgebraicGeometry.Scheme.Zariski.Small.ringedHom f).modulePullback.obj
        (AlgebraicGeometry.Scheme.SiteRestriction.sourceSmallZariskiView Y F)) :
    (AlgebraicGeometry.Scheme.Zariski.Small.ringedHom f).modulePullback.obj
          (AlgebraicGeometry.Scheme.SiteRestriction.sourceSmallZariskiView Y F) ≅
      (AlgebraicGeometry.Scheme.Zariski.Small.ringedHom f).modulePullback.obj
        (AlgebraicGeometry.Scheme.SiteRestriction.sourceSmallZariskiView Y F))

end
