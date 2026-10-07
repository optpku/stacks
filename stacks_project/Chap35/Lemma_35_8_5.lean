module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.PullbackSections

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 35.8.5 (1): inverse image from the small Zariski site to the big
`τ`-site is the `τ`-sheafification of `f : T ⟶ S ↦ Γ(T, f^*F)`. -/
@[stacks 070S] #check
  (AlgebraicGeometry.Scheme.SiteRestriction.bigZariskiIso :
    ∀ (τ : StandardTopology) (S : Scheme.{u})
        (F : RingedSite.ModuleCat.{u}
          (AlgebraicGeometry.Scheme.Zariski.Small.ringedSite S)),
      (AlgebraicGeometry.Scheme.SiteRestriction.bigToZariski τ S).modulePullback.obj F ≅
        (_root_.PresheafOfModules.sheafification
          (𝟙 (StandardTopology.Big.structureSheaf τ S).obj)).obj
            (AlgebraicGeometry.Scheme.SiteRestriction.bigZariskiPullbackSections τ S F))

/- The big-site presheaf in the first clause is exactly the module presheaf
`f : T ⟶ S ↦ Γ(T, f^*F)`. -/
#check
  (AlgebraicGeometry.Scheme.SiteRestriction.bigZariskiPullbackSections_sourceView :
    ∀ (τ : StandardTopology) (S : Scheme.{u}) (F : S.Modules),
      AlgebraicGeometry.Scheme.SiteRestriction.bigZariskiPullbackSections τ S
          (AlgebraicGeometry.Scheme.SiteRestriction.sourceSmallZariskiView S F) =
        AlgebraicGeometry.Scheme.Modules.PullbackSections.modulePresheaf
          (𝟭 (Over S)) F)

/- Lemma 35.8.5 (2): inverse image from the small Zariski site to the small
étale site is the étale sheafification of `f : T ⟶ S ↦ Γ(T, f^*F)`. -/
@[stacks 070S] #check
  (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleZariskiIso :
    ∀ (S : Scheme.{u})
        (F : RingedSite.ModuleCat.{u}
          (AlgebraicGeometry.Scheme.Zariski.Small.ringedSite S)),
      (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleToZariski S).modulePullback.obj F ≅
        (_root_.PresheafOfModules.sheafification
          (𝟙 (AlgebraicGeometry.Scheme.Etale.Small.structureSheaf S).obj)).obj
            (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleZariskiPullbackSections S F))

/- The small-étale presheaf in the second clause is exactly the module
presheaf `f : T ⟶ S ↦ Γ(T, f^*F)`. -/
#check
  (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleZariskiPullbackSections_sourceView :
    ∀ (S : Scheme.{u}) (F : S.Modules),
      AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleZariskiPullbackSections S
          (AlgebraicGeometry.Scheme.SiteRestriction.sourceSmallZariskiView S F) =
        AlgebraicGeometry.Scheme.Modules.PullbackSections.modulePresheaf
          (AlgebraicGeometry.Scheme.Etale.forget S) F)

/- Lemma 35.8.5 (3): for non-Zariski `τ`, inverse image from the small étale
site to the big `τ`-site is the `τ`-sheafification of
`f : T ⟶ S ↦ Γ(T, f_small^*G)`. -/
@[stacks 070S] #check
  (AlgebraicGeometry.Scheme.SiteRestriction.bigEtaleIso :
    ∀ (τ : StandardTopology) (S : Scheme.{u}) (hτ : τ ≠ .zariski)
        (G : RingedSite.ModuleCat.{u}
          (AlgebraicGeometry.Scheme.Etale.Small.ringedSite S)),
      (AlgebraicGeometry.Scheme.SiteRestriction.bigToEtale τ S hτ).modulePullback.obj G ≅
        (_root_.PresheafOfModules.sheafification
          (𝟙 (StandardTopology.Big.structureSheaf τ S).obj)).obj
            (AlgebraicGeometry.Scheme.Etale.Modules.PullbackSections.over τ S hτ G))

/- Objectwise, the presheaf in the third clause has value
`Γ(T, f_small^*G)`. -/
#check
  (AlgebraicGeometry.Scheme.Etale.Modules.PullbackSections.over_obj :
    ∀ (τ : StandardTopology) (S : Scheme.{u}) (hτ : τ ≠ .zariski)
        (G : RingedSite.ModuleCat.{u}
          (AlgebraicGeometry.Scheme.Etale.Small.ringedSite S))
        (U : (Over S)ᵒᵖ),
      (AlgebraicGeometry.Scheme.Etale.Modules.PullbackSections.over τ S hτ G).obj U =
        ((AlgebraicGeometry.Scheme.Etale.Small.ringedHom U.unop.hom).modulePullback.obj
          G).val.obj
            (Opposite.op
              (AlgebraicGeometry.Scheme.Etale.mk
                (X := U.unop.left) (Y := U.unop.left)
                (CategoryStruct.id (obj := Scheme.{u}) U.unop.left))))

/- Restriction in the presheaf of the third clause is the canonical pullback
restriction map. -/
#check
  (AlgebraicGeometry.Scheme.Etale.Modules.PullbackSections.over_map :
    ∀ (τ : StandardTopology) (S : Scheme.{u}) (hτ : τ ≠ .zariski)
        (G : RingedSite.ModuleCat.{u}
          (AlgebraicGeometry.Scheme.Etale.Small.ringedSite S))
        {U V : (Over S)ᵒᵖ} (f : U ⟶ V),
      (AlgebraicGeometry.Scheme.Etale.Modules.PullbackSections.over τ S hτ G).map f =
        ((_root_.PresheafOfModules.pullback.{u}
          (AlgebraicGeometry.Scheme.SiteRestriction.bigToEtale τ S hτ).structureSheafMap.hom).obj
            G.val).map f)
