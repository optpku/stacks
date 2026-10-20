module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.LocalComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.PresentationComparison
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward.Composition
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! # Structure modules and presentations of scheme restriction -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry (Scheme)

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme

variable {S : Scheme.{u}}

/-- The ringed-site composite from the small étale site of `ofOver U` to the open-subscheme
ringed site of `U.left`. -/
noncomputable def restrictToOpensHom (U : Over S) :
    RingedSite.Hom (ringedSite (ofOver U))
      (RingedSite.ofRingSheaf (Opens.grothendieckTopology (U.left : TopCat))
        ⟨Scheme.Site.structurePresheaf (U.left.restrictFunctor ⋙ Over.forget U.left),
          opensStructurePresheaf_isSheaf U.left⟩) :=
  RingedSite.Hom.comp (schemeEtaleRingedHom U) (smallEtaleToOpensRingedHom U.left)

/-- Continuity of the named restriction functor, projected from its ringed-site morphism. -/
theorem restrictToOpensHom_isContinuous (U : Over S) :
    (restrictToOpensHom U).base.IsContinuous
      (Opens.grothendieckTopology (U.left : TopCat)) (smallEtaleTopology (ofOver U)) :=
  RingedSite.Hom.base_isContinuous (restrictToOpensHom U)

/-- Identification of the two-stage module pushforward in `restrictToScheme` with pushforward
along `restrictToOpensHom`. -/
noncomputable def restrictToOpensPushforwardIso (U : Over S) :
    (schemeEtaleRingedHom U).modulePushforward.{u} ⋙
        (smallEtaleToOpensRingedHom U.left).modulePushforward.{u} ≅
      (restrictToOpensHom U).modulePushforward.{u} :=
  RingedSite.Hom.modulePushforwardCompIso.{u}
    (schemeEtaleRingedHom U) (smallEtaleToOpensRingedHom U.left)

/-- Transport of `restrictToScheme` along the module-pushforward composite of
`restrictToOpensHom`. -/
noncomputable def restrictToSchemeOpensIso {U : Over S} (F : (ofOver U).Modules) :
    (Modules.restrictToScheme U).obj F ≅
      (opensToSchemeModules U.left).obj
        ((restrictToOpensHom U).modulePushforward.{u}.obj
          ((Modules.restrictFunctor (𝟙 (ofOver U))).obj F)) :=
  (Modules.RestrictToScheme.restrictionIsoBare U).app F ≪≫
    (Modules.RestrictToScheme.restrictionBare U).mapIso
      ((Modules.RestrictToScheme.identityRestrictionIso U).app F).symm ≪≫
    (opensToSchemeModules U.left).mapIso
      ((restrictToOpensPushforwardIso U).app ((Modules.restrictFunctor (𝟙 (ofOver U))).obj F))

/-- Restriction to the underlying scheme preserves zero module morphisms. -/
instance preservesZeroMorphisms (U : Over S) :
    (Modules.restrictToScheme U).PreservesZeroMorphisms := sorry

/-- The coefficient comparison identifies the scheme and restricted structure modules. -/
instance unitMap_isIso (U : Over S) : IsIso (unitMap U) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme
