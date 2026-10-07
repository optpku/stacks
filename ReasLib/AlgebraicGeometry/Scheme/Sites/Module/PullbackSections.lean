module

public import ReasLib.AlgebraicGeometry.Scheme.Module.PullbackSections
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Restriction

/-!
# Pullback sections on standard scheme sites

This file identifies inverse images of modules along the standard restriction
morphisms with sheafifications of their pullback-sections presheaves.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.SiteRestriction

/-- The identity of `T`, viewed as the terminal object of its small Zariski site. -/
def smallZariskiTerminal (T : Scheme.{u}) : T.smallZariskiSite :=
  MorphismProperty.Over.mk _ (𝟙 T) inferInstance

/-- The structure morphism of `smallZariskiTerminal T` is the identity of `T`. -/
theorem smallZariskiTerminal_hom (T : Scheme.{u}) :
    (smallZariskiTerminal T).hom = 𝟙 T := sorry

/-- The pullback-sections presheaf on the big `τ`-site associated to a module on
the small Zariski site. -/
noncomputable def bigZariskiPullbackSections
    (τ : StandardTopology) (S : Scheme.{u})
    (F : RingedSite.ModuleCat.{u} (Scheme.Zariski.Small.ringedSite S)) :
    _root_.PresheafOfModules.{u} (StandardTopology.Big.structureSheaf τ S).obj :=
  (_root_.PresheafOfModules.pullback.{u}
    (bigToZariski τ S).structureSheafMap.hom).obj F.val

/-- The big-site pullback-sections presheaf is the canonical presheaf pullback. -/
theorem bigZariskiPullbackSections_def
    (τ : StandardTopology) (S : Scheme.{u})
    (F : RingedSite.ModuleCat.{u} (Scheme.Zariski.Small.ringedSite S)) :
    bigZariskiPullbackSections τ S F =
      (_root_.PresheafOfModules.pullback.{u}
        (bigToZariski τ S).structureSheafMap.hom).obj F.val := sorry

/-- At `f : T ⟶ S`, the big-site pullback-sections presheaf is the module of
global sections of the pullback of `F` to `T`. -/
theorem bigZariskiPullbackSections_obj
    (τ : StandardTopology) (S : Scheme.{u})
    (F : RingedSite.ModuleCat.{u} (Scheme.Zariski.Small.ringedSite S))
    (U : Over S) :
    (bigZariskiPullbackSections τ S F).obj (Opposite.op U) =
      ((Scheme.Zariski.Small.ringedHom U.hom).modulePullback.obj F).val.obj
        (Opposite.op (smallZariskiTerminal U.left)) := sorry

/-- The canonical inverse-image/sheafification isomorphism for restriction from
the small Zariski site to the big `τ`-site. -/
noncomputable def bigZariskiIso
    (τ : StandardTopology) (S : Scheme.{u})
    (F : RingedSite.ModuleCat.{u} (Scheme.Zariski.Small.ringedSite S)) :
    (bigToZariski τ S).modulePullback.obj F ≅
      (_root_.PresheafOfModules.sheafification
        (𝟙 (StandardTopology.Big.structureSheaf τ S).obj)).obj
          (bigZariskiPullbackSections τ S F) :=
  (@SheafOfModules.pullbackIso
    _ _ _ _ _ _ _ _ _
    (RingedSite.Hom.base_isContinuous (bigToZariski τ S))
    (bigToZariski τ S).structureSheafMap
    (bigToZariski_presheafPushforward_isRightAdjoint τ S)
    (big_hasWeakSheafify τ S) (big_wEqualsLocallyBijective τ S)).app F

/-- The topology on the small étale category induced by the big Zariski topology. -/
def smallEtaleZariskiTopology (S : Scheme.{u}) : GrothendieckTopology S.Etale :=
  (Scheme.Etale.forget S).inducedTopology
    (StandardTopology.zariski.overTopology S)

/-- The small-étale Zariski topology is induced along the forgetful functor to
schemes over `S`. -/
theorem smallEtaleZariskiTopology_def (S : Scheme.{u}) :
    smallEtaleZariskiTopology S =
      (Scheme.Etale.forget S).inducedTopology
        (StandardTopology.zariski.overTopology S) := sorry

/-- The pullback-sections presheaf on the small étale site associated to a
module on the small Zariski site. -/
noncomputable def smallEtaleZariskiPullbackSections
    (S : Scheme.{u})
    (F : RingedSite.ModuleCat.{u} (Scheme.Zariski.Small.ringedSite S)) :
    _root_.PresheafOfModules.{u} (Scheme.Etale.Small.structureSheaf S).obj :=
  (_root_.PresheafOfModules.pullback.{u}
    (smallEtaleToZariski S).structureSheafMap.hom).obj F.val

/-- The small-étale pullback-sections presheaf is the canonical presheaf pullback. -/
theorem smallEtaleZariskiPullbackSections_def
    (S : Scheme.{u})
    (F : RingedSite.ModuleCat.{u} (Scheme.Zariski.Small.ringedSite S)) :
    smallEtaleZariskiPullbackSections S F =
      (_root_.PresheafOfModules.pullback.{u}
        (smallEtaleToZariski S).structureSheafMap.hom).obj F.val := sorry

/-- At an étale map `f : T ⟶ S`, the pullback-sections presheaf is the module
of global sections of the pullback of `F` to `T`. -/
theorem smallEtaleZariskiPullbackSections_obj
    (S : Scheme.{u})
    (F : RingedSite.ModuleCat.{u} (Scheme.Zariski.Small.ringedSite S))
    (U : S.Etale) :
    (smallEtaleZariskiPullbackSections S F).obj (Opposite.op U) =
      ((Scheme.Zariski.Small.ringedHom U.hom).modulePullback.obj F).val.obj
        (Opposite.op (smallZariskiTerminal U.left)) := sorry

/-- The canonical inverse-image/sheafification isomorphism from the small
Zariski site to the small étale site. -/
noncomputable def smallEtaleZariskiIso
    (S : Scheme.{u})
    (F : RingedSite.ModuleCat.{u} (Scheme.Zariski.Small.ringedSite S)) :
    (smallEtaleToZariski S).modulePullback.obj F ≅
      (_root_.PresheafOfModules.sheafification
        (𝟙 (Scheme.Etale.Small.structureSheaf S).obj)).obj
          (smallEtaleZariskiPullbackSections S F) :=
  (@SheafOfModules.pullbackIso
    _ _ _ _ _ _ _ _ _
    (RingedSite.Hom.base_isContinuous (smallEtaleToZariski S))
    (smallEtaleToZariski S).structureSheafMap
    (smallEtaleToZariski_presheafPushforward_isRightAdjoint S)
    (smallEtale_hasWeakSheafify S) (smallEtale_wEqualsLocallyBijective S)).app F

end AlgebraicGeometry.Scheme.SiteRestriction

namespace AlgebraicGeometry.Scheme.Etale.Modules.PullbackSections

/-- The pullback-sections presheaf on the big `τ`-site associated to a module
on the small étale site. -/
noncomputable def over (τ : StandardTopology) (S : Scheme.{u})
    (hτ : τ ≠ .zariski)
    (G : RingedSite.ModuleCat.{u} (Scheme.Etale.Small.ringedSite S)) :
    _root_.PresheafOfModules.{u} (StandardTopology.Big.structureSheaf τ S).obj :=
  (_root_.PresheafOfModules.pullback.{u}
    (Scheme.SiteRestriction.bigToEtale τ S hτ).structureSheafMap.hom).obj G.val

/-- The étale pullback-sections presheaf is the canonical presheaf pullback. -/
theorem over_def (τ : StandardTopology) (S : Scheme.{u})
    (hτ : τ ≠ .zariski)
    (G : RingedSite.ModuleCat.{u} (Scheme.Etale.Small.ringedSite S)) :
    over τ S hτ G =
      (_root_.PresheafOfModules.pullback.{u}
        (Scheme.SiteRestriction.bigToEtale τ S hτ).structureSheafMap.hom).obj
          G.val := sorry

/-- At `f : T ⟶ S`, the presheaf `over τ S hτ G` is the module of global
sections of the small-étale pullback of `G` to `T`. -/
theorem over_obj (τ : StandardTopology) (S : Scheme.{u})
    (hτ : τ ≠ .zariski)
    (G : RingedSite.ModuleCat.{u} (Scheme.Etale.Small.ringedSite S))
    (U : (Over S)ᵒᵖ) :
    (over τ S hτ G).obj U =
      ((Scheme.Etale.Small.ringedHom U.unop.hom).modulePullback.obj G).val.obj
        (Opposite.op
          (Scheme.Etale.mk (X := U.unop.left) (Y := U.unop.left)
            (CategoryStruct.id (obj := Scheme.{u}) U.unop.left))) := sorry

/-- Restriction in `over τ S hτ G` is the restriction map of the canonical
presheaf pullback. -/
theorem over_map (τ : StandardTopology) (S : Scheme.{u})
    (hτ : τ ≠ .zariski)
    (G : RingedSite.ModuleCat.{u} (Scheme.Etale.Small.ringedSite S))
    {U V : (Over S)ᵒᵖ} (f : U ⟶ V) :
    (over τ S hτ G).map f =
      ((_root_.PresheafOfModules.pullback.{u}
        (Scheme.SiteRestriction.bigToEtale τ S hτ).structureSheafMap.hom).obj
          G.val).map f := sorry

end AlgebraicGeometry.Scheme.Etale.Modules.PullbackSections

namespace AlgebraicGeometry.Scheme.SiteRestriction

/-- The canonical inverse-image/sheafification isomorphism from the small
étale site to the big `τ`-site. -/
noncomputable def bigEtaleIso
    (τ : StandardTopology) (S : Scheme.{u}) (hτ : τ ≠ .zariski)
    (G : RingedSite.ModuleCat.{u} (Scheme.Etale.Small.ringedSite S)) :
    (bigToEtale τ S hτ).modulePullback.obj G ≅
      (_root_.PresheafOfModules.sheafification
        (𝟙 (StandardTopology.Big.structureSheaf τ S).obj)).obj
          (Etale.Modules.PullbackSections.over τ S hτ G) :=
  (@SheafOfModules.pullbackIso
    _ _ _ _ _ _ _ _ _
    (RingedSite.Hom.base_isContinuous (bigToEtale τ S hτ))
    (bigToEtale τ S hτ).structureSheafMap
    (bigToEtale_presheafPushforward_isRightAdjoint τ S hτ)
    (big_hasWeakSheafify τ S) (big_wEqualsLocallyBijective τ S)).app G

/-- The pullback-sections presheaf of a scheme module is a sheaf on the explicit
small Zariski site. -/
theorem sourceSmallZariskiView_isSheaf (S : Scheme.{u}) (F : S.Modules) :
    Presheaf.IsSheaf S.smallZariskiTopology
      (Scheme.Modules.PullbackSections.modulePresheaf
        S.smallZariskiForget F).presheaf := sorry

/-- A scheme module viewed on the global-sections small Zariski ringed site by
the formula `U ↦ Γ(U, F|_U)`. -/
noncomputable def sourceSmallZariskiView (S : Scheme.{u}) (F : S.Modules) :
    RingedSite.ModuleCat.{u} (Zariski.Small.ringedSite S) :=
  ⟨Scheme.Modules.PullbackSections.modulePresheaf S.smallZariskiForget F,
    sourceSmallZariskiView_isSheaf S F⟩

/-- The underlying presheaf of `sourceSmallZariskiView` is the
pullback-sections module presheaf. -/
theorem sourceSmallZariskiView_val (S : Scheme.{u}) (F : S.Modules) :
    (sourceSmallZariskiView S F).val =
      Scheme.Modules.PullbackSections.modulePresheaf
        S.smallZariskiForget F := sorry

/-- Pulling the source view to a standard big site yields the module presheaf
`f : T ⟶ S ↦ Γ(T, f^*F)`. -/
theorem bigZariskiPullbackSections_sourceView
    (τ : StandardTopology) (S : Scheme.{u}) (F : S.Modules) :
    bigZariskiPullbackSections τ S (sourceSmallZariskiView S F) =
      Scheme.Modules.PullbackSections.modulePresheaf (𝟭 (Over S)) F := sorry

/-- Pulling the source view to the small étale site yields the module presheaf
`f : T ⟶ S ↦ Γ(T, f^*F)`. -/
theorem smallEtaleZariskiPullbackSections_sourceView
    (S : Scheme.{u}) (F : S.Modules) :
    smallEtaleZariskiPullbackSections S (sourceSmallZariskiView S F) =
      Scheme.Modules.PullbackSections.modulePresheaf
        (Scheme.Etale.forget S) F := sorry

/-- The presheaf `f : T ⟶ S ↦ Γ(T, f^*F)` is a sheaf for the big Zariski
topology. -/
theorem bigZariskiPullbackSections_isSheafZariski
    (S : Scheme.{u}) (F : S.Modules) :
    Presheaf.IsSheaf (StandardTopology.zariski.overTopology S)
      (Scheme.Modules.PullbackSections.modulePresheaf
        (𝟭 (Over S)) F).presheaf := sorry

/-- The presheaf `f : T ⟶ S ↦ Γ(T, f^*F)` on the small étale category is a
sheaf for its induced Zariski topology. -/
theorem smallEtalePullbackSections_isSheafZariski
    (S : Scheme.{u}) (F : S.Modules) :
    Presheaf.IsSheaf (smallEtaleZariskiTopology S)
      (Scheme.Modules.PullbackSections.modulePresheaf
        (Scheme.Etale.forget S) F).presheaf := sorry

end AlgebraicGeometry.Scheme.SiteRestriction

namespace AlgebraicGeometry.Scheme.Etale.Modules.PullbackSections

/-- The presheaf `f : T ⟶ S ↦ Γ(T, f_small^*G)` is an étale sheaf on every
non-Zariski standard big site. -/
theorem isSheaf
    (τ : StandardTopology) (S : Scheme.{u}) (hτ : τ ≠ .zariski)
    (G : RingedSite.ModuleCat.{u} (Etale.Small.ringedSite S)) :
    Presheaf.IsSheaf (StandardTopology.etale.overTopology S)
      (over τ S hτ G).presheaf := sorry

end AlgebraicGeometry.Scheme.Etale.Modules.PullbackSections
