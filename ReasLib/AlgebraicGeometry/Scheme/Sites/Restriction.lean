module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed

/-!
# Restriction morphisms between standard scheme sites

This file constructs the canonical restriction morphisms among the standard
big, small Zariski, and small étale ringed sites of a scheme.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.SiteRestriction

/-- The canonical functor from the small Zariski site of `S` to its small étale site. -/
def smallZariskiToSmallEtale (S : Scheme.{u}) :
    S.smallZariskiSite ⥤ S.Etale :=
  MorphismProperty.Comma.lift S.smallZariskiForget
    (fun _ ↦ sorry) (fun _ ↦ trivial) (fun _ ↦ trivial)

/-- Forgetting the étale structure after `smallZariskiToSmallEtale` recovers the
small-Zariski forgetful functor. -/
theorem smallZariskiToSmallEtale_comp_forget (S : Scheme.{u}) :
    smallZariskiToSmallEtale S ⋙ Scheme.Etale.forget S = S.smallZariskiForget := sorry

/-- The small-Zariski inclusion is a morphism to every standard big site. -/
instance smallZariskiForget_isMorphismOfSites
    (τ : StandardTopology) (S : Scheme.{u}) :
    IsMorphismOfSites S.smallZariskiTopology (τ.overTopology S)
      S.smallZariskiForget := sorry

/-- The small-Zariski inclusion is continuous into every standard big site. -/
instance smallZariskiForget_isContinuous
    (τ : StandardTopology) (S : Scheme.{u}) :
    S.smallZariskiForget.IsContinuous S.smallZariskiTopology
      (τ.overTopology S) := sorry

/-- The inclusion from the small Zariski site to the small étale site is a
morphism of sites. -/
instance smallZariskiToSmallEtale_isMorphismOfSites (S : Scheme.{u}) :
    IsMorphismOfSites S.smallZariskiTopology S.smallEtaleTopology
      (smallZariskiToSmallEtale S) := sorry

/-- The inclusion from the small Zariski site to the small étale site is continuous. -/
instance smallZariskiToSmallEtale_isContinuous (S : Scheme.{u}) :
    (smallZariskiToSmallEtale S).IsContinuous S.smallZariskiTopology
      S.smallEtaleTopology := sorry

/-- For each non-Zariski standard topology, the small-étale forgetful functor is
a morphism to the corresponding big site. -/
theorem smallEtaleForget_isMorphismOfSites
    (τ : StandardTopology) (S : Scheme.{u}) (hτ : τ ≠ .zariski) :
    IsMorphismOfSites S.smallEtaleTopology (τ.overTopology S)
      (Scheme.Etale.forget S) := sorry

/-- For each non-Zariski standard topology, the small-étale forgetful functor is
continuous into the corresponding big site. -/
theorem smallEtaleForget_isContinuous
    (τ : StandardTopology) (S : Scheme.{u}) (hτ : τ ≠ .zariski) :
    (Scheme.Etale.forget S).IsContinuous S.smallEtaleTopology
      (τ.overTopology S) := sorry

/-- The ringed-site morphism from the big `τ`-site to the small Zariski site. -/
noncomputable def bigToZariski (τ : StandardTopology) (S : Scheme.{u}) :
    RingedSite.Hom (StandardTopology.Big.ringedSite τ S)
      (Scheme.Zariski.Small.ringedSite S) :=
  Scheme.Site.ringedHom S.smallZariskiTopology (τ.overTopology S)
    (Scheme.smallZariskiToScheme S) (Over.forget S) S.smallZariskiForget
    (𝟙 (Scheme.smallZariskiToScheme S))
    (Scheme.Zariski.Small.structurePresheaf_isSheaf S)
    (StandardTopology.Big.structurePresheaf_isSheaf τ S)

/-- The base functor of `bigToZariski` is the canonical small-site inclusion. -/
theorem bigToZariski_base (τ : StandardTopology) (S : Scheme.{u}) :
    (bigToZariski τ S).base = S.smallZariskiForget := sorry

/-- The ringed-site morphism from the small étale site to the small Zariski site. -/
noncomputable def smallEtaleToZariski (S : Scheme.{u}) :
    RingedSite.Hom (Scheme.Etale.Small.ringedSite S)
      (Scheme.Zariski.Small.ringedSite S) :=
  Scheme.Site.ringedHom S.smallZariskiTopology S.smallEtaleTopology
    (Scheme.smallZariskiToScheme S) (Scheme.smallEtaleToScheme S)
    (smallZariskiToSmallEtale S) (𝟙 (Scheme.smallZariskiToScheme S))
    (Scheme.Zariski.Small.structurePresheaf_isSheaf S)
    (Scheme.Etale.Small.structurePresheaf_isSheaf S)

/-- The base of `smallEtaleToZariski` is the inclusion of open immersions among
étale morphisms. -/
theorem smallEtaleToZariski_base (S : Scheme.{u}) :
    (smallEtaleToZariski S).base = smallZariskiToSmallEtale S := sorry

/-- The ringed-site morphism from the big `τ`-site to the small étale site for a
non-Zariski standard topology `τ`. -/
noncomputable def bigToEtale (τ : StandardTopology) (S : Scheme.{u})
    (hτ : τ ≠ .zariski) :
    RingedSite.Hom (StandardTopology.Big.ringedSite τ S)
      (Scheme.Etale.Small.ringedSite S) where
  base := Scheme.Etale.forget S
  isMorphismOfSites := smallEtaleForget_isMorphismOfSites τ S hτ
  structureSheafMap :=
    @Scheme.Site.structureSheafMap _ _ _ _ S.smallEtaleTopology
      (τ.overTopology S) (Scheme.smallEtaleToScheme S) (Over.forget S)
      (Scheme.Etale.forget S) (smallEtaleForget_isContinuous τ S hτ)
      (𝟙 (Scheme.smallEtaleToScheme S))
      (Scheme.Etale.Small.structurePresheaf_isSheaf S)
      (StandardTopology.Big.structurePresheaf_isSheaf τ S)

/-- The base of `bigToEtale` is the canonical forgetful functor to schemes over `S`. -/
theorem bigToEtale_base (τ : StandardTopology) (S : Scheme.{u})
    (hτ : τ ≠ .zariski) :
    (bigToEtale τ S hτ).base = Scheme.Etale.forget S := sorry

/-- Abelian-group-valued weak sheafification exists on every standard big site. -/
instance big_hasWeakSheafify (τ : StandardTopology) (S : Scheme.{u}) :
    HasWeakSheafify (τ.overTopology S) AddCommGrpCat.{u} := sorry

/-- On every standard big site, sheafification equivalences are the locally
bijective morphisms. -/
instance big_wEqualsLocallyBijective (τ : StandardTopology) (S : Scheme.{u}) :
    (τ.overTopology S).WEqualsLocallyBijective AddCommGrpCat.{u} := sorry

/-- Abelian-group-valued weak sheafification exists on the small étale site. -/
instance smallEtale_hasWeakSheafify (S : Scheme.{u}) :
    HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u} := sorry

/-- On the small étale site, sheafification equivalences are the locally
bijective morphisms. -/
instance smallEtale_wEqualsLocallyBijective (S : Scheme.{u}) :
    S.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u} := sorry

/-- Presheaf module pushforward along `bigToZariski` admits its canonical left adjoint. -/
instance bigToZariski_presheafPushforward_isRightAdjoint
    (τ : StandardTopology) (S : Scheme.{u}) :
    (PresheafOfModules.pushforward.{u}
      (bigToZariski τ S).structureSheafMap.hom).IsRightAdjoint := sorry

/-- Presheaf module pushforward along `smallEtaleToZariski` admits its canonical
left adjoint. -/
instance smallEtaleToZariski_presheafPushforward_isRightAdjoint
    (S : Scheme.{u}) :
    (PresheafOfModules.pushforward.{u}
      (smallEtaleToZariski S).structureSheafMap.hom).IsRightAdjoint := sorry

/-- Presheaf module pushforward along `bigToEtale` admits its canonical left adjoint. -/
instance bigToEtale_presheafPushforward_isRightAdjoint
    (τ : StandardTopology) (S : Scheme.{u}) (hτ : τ ≠ .zariski) :
    (PresheafOfModules.pushforward.{u}
      (bigToEtale τ S hτ).structureSheafMap.hom).IsRightAdjoint := sorry

/-- Module pushforward along `bigToZariski` has the canonical inverse-image left adjoint. -/
noncomputable instance bigToZariski_modulePushforward_isRightAdjoint
    (τ : StandardTopology) (S : Scheme.{u}) :
    ((bigToZariski τ S).modulePushforward.{u}).IsRightAdjoint := sorry

/-- Module pushforward along `smallEtaleToZariski` has the canonical inverse-image
left adjoint. -/
noncomputable instance smallEtaleToZariski_modulePushforward_isRightAdjoint
    (S : Scheme.{u}) :
    ((smallEtaleToZariski S).modulePushforward.{u}).IsRightAdjoint := sorry

/-- Module pushforward along `bigToEtale` has the canonical inverse-image left adjoint. -/
noncomputable instance bigToEtale_modulePushforward_isRightAdjoint
    (τ : StandardTopology) (S : Scheme.{u}) (hτ : τ ≠ .zariski) :
    ((bigToEtale τ S hτ).modulePushforward.{u}).IsRightAdjoint := sorry

/-- Module pushforward along a small-Zariski pullback morphism has the canonical
inverse-image left adjoint. -/
noncomputable instance smallZariskiRingedHom_modulePushforward_isRightAdjoint
    {S T : Scheme.{u}} (f : T ⟶ S) :
    ((Scheme.Zariski.Small.ringedHom f).modulePushforward.{u}).IsRightAdjoint := sorry

/-- Module pushforward along a small-étale pullback morphism has the canonical
inverse-image left adjoint. -/
noncomputable instance smallEtaleRingedHom_modulePushforward_isRightAdjoint
    {S T : Scheme.{u}} (f : T ⟶ S) :
    ((Scheme.Etale.Small.ringedHom f).modulePushforward.{u}).IsRightAdjoint := sorry

end AlgebraicGeometry.Scheme.SiteRestriction
