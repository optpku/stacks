module

public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import ReasLib.CategoryTheory.Sites.FullyFaithful
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import stacks_project.Chap66.Lemma_66_18_8_Pullback
public import stacks_project.Chap73.Lemma_73_4_7_Relocalization

/-!
# Identity-base spaces-étale to big étale relocalization

This leaf owns the identity-base extras of Sites Lemma 7.21.8 for an algebraic
space `X`: the inclusion `X_spaces,étale ⥤ (Spaces/X)_étale` is a morphism of
sites, induces `π_X`, and retracts the relocalization morphism `i_{id_X}`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u w

namespace AlgebraicGeometry.AlgebraicSpace
namespace Etale
namespace SpacesToBig

section Identity

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- The identity-base relocalization is canonically isomorphic to the inclusion
of the spaces-étale site into the big étale slice. -/
def relocalizationFunctor_id_iso :
    relocalizationFunctor (𝟙 X) ≅ MorphismProperty.Over.forget (@Etale S) ⊤ X :=
  Functor.isoWhiskerLeft (MorphismProperty.Over.forget (@Etale S) ⊤ X) (Over.mapId X) ≪≫
    Functor.rightUnitor (MorphismProperty.Over.forget (@Etale S) ⊤ X)

/-- The identity-base relocalization is full. -/
instance relocalizationFunctor_id_full :
    (relocalizationFunctor (𝟙 X)).Full := sorry

/-- The identity-base relocalization is faithful. -/
instance relocalizationFunctor_id_faithful :
    (relocalizationFunctor (𝟙 X)).Faithful := sorry

/-- The identity-base relocalization sends the spaces-étale terminal object `X/X`
to a terminal object of the big étale slice. -/
noncomputable def relocalizationFunctor_id_obj_isTerminal :
    IsTerminal ((relocalizationFunctor (𝟙 X)).obj (spacesEtaleSite.self X)) :=
  IsTerminal.ofIso Over.mkIdTerminal
    ((relocalizationFunctor_id_iso X).app (spacesEtaleSite.self X)).symm

/-- The identity-base relocalization is a morphism of spaces-étale to big étale
sites. -/
instance identity_isMorphismOfSites :
    IsMorphismOfSites (spacesEtaleTopology X) (overEtaleTopology X)
      (relocalizationFunctor (𝟙 X)) := sorry

/-- The inverse image of the identity-base spaces-to-big site morphism preserves
finite limits. -/
instance identity_sheafPullback_preservesFiniteLimits
    [HasWeakSheafify (overEtaleTopology X) (Type w)] :
    PreservesFiniteLimits
      ((relocalizationFunctor (𝟙 X)).sheafPullback (Type w)
        (spacesEtaleTopology X) (overEtaleTopology X)) := sorry

/-- The morphism of topoi induced by the identity-base spaces-to-big étale site
morphism. -/
noncomputable def siteMorphismOfTopoi
    [HasWeakSheafify (overEtaleTopology X) (Type w)] :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, w}
      (spacesEtaleTopology X) (overEtaleTopology X) :=
  Functor.morphismOfTopoiInOfContinuous.{w, u + 1, u + 1, u + 1, u + 1}
    (relocalizationFunctor (𝟙 X)) (spacesEtaleTopology X) (overEtaleTopology X)

/-- For identity-base spaces-étale relocalization, the inverse image of `i_X`
equals the direct image of the induced site morphism `π_X`. -/
theorem morphismOfTopoi_id_inverseImage_eq_siteMorphismOfTopoi_pushforward
    [HasWeakSheafify (overEtaleTopology X) (Type w)]
    [HasSheafify (spacesEtaleTopology X) (Type w)] :
    (morphismOfTopoi (𝟙 X))⁻¹ = (siteMorphismOfTopoi X).pushforward := sorry

/-- The composite inverse image of the identity-base site morphism `π_X` and the
relocalization morphism `i_{id_X}` is naturally isomorphic to the identity. -/
noncomputable def siteMorphismOfTopoi_comp_morphismOfTopoi_id
    [HasWeakSheafify (overEtaleTopology X) (Type w)]
    [HasSheafify (spacesEtaleTopology X) (Type w)] :
    (MorphismOfTopoiIn.comp (siteMorphismOfTopoi X) (morphismOfTopoi (𝟙 X))).inverseImage ≅
      (MorphismOfTopoiIn.id (spacesEtaleTopology X)).inverseImage :=
  (asIso
    ((relocalizationFunctor (𝟙 X)).sheafAdjunctionContinuous (Type w)
      (spacesEtaleTopology X) (overEtaleTopology X)).unit).symm

/-- The direct image of the identity-base site morphism is computed by
evaluation on relocalized spaces-étale objects. -/
theorem siteMorphismOfTopoi_pushforward_obj_obj
    [HasWeakSheafify (overEtaleTopology X) (Type w)]
    (𝒢 : Sheaf (overEtaleTopology X) (Type w)) (U : spacesEtaleSite X) :
    ((siteMorphismOfTopoi X).pushforward.obj 𝒢).1.obj (op U) =
      𝒢.1.obj (op ((relocalizationFunctor (𝟙 X)).obj U)) := sorry

end Identity

end SpacesToBig
end Etale
end AlgebraicGeometry.AlgebraicSpace
