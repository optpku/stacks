module

public import stacks_project.Chap61.Lemma_61_12_12_SmallToBig
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import Mathlib.CategoryTheory.Whiskering

/-!
# Identity-base small-to-big pro-étale relocalization

This leaf owns the identity-base extras of Sites Lemma 7.21.8 for a chosen big
pro-étale site containing `S`: the small-to-big inclusion is a morphism of
sites, induces `π_S`, and retracts the relocalization morphism `i_{id_S}`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped MorphismOfTopoiIn

noncomputable section

universe u v w

namespace AlgebraicGeometry.ChosenBigProetaleSite
namespace SmallToBig

section Identity

variable (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier)

/-- The identity-base relocalization is canonically isomorphic to the inclusion
of the chosen small pro-étale site. -/
def relocalizationFunctor_id_iso :
    relocalizationFunctor (𝟙 S) ≅ smallInclusion X S :=
  Functor.isoWhiskerLeft (smallInclusion X S) (Over.mapId S) ≪≫
    Functor.rightUnitor (smallInclusion X S)

/-- The identity-base relocalization is full. -/
instance relocalizationFunctor_id_full :
    (relocalizationFunctor (𝟙 S)).Full := sorry

/-- The identity-base relocalization is faithful. -/
instance relocalizationFunctor_id_faithful :
    (relocalizationFunctor (𝟙 S)).Faithful := sorry

/-- The identity-base relocalization sends the small-site terminal object `S/S`
to a terminal object of the chosen big slice. -/
noncomputable def relocalizationFunctor_id_obj_isTerminal :
    IsTerminal ((relocalizationFunctor (𝟙 S)).obj (smallTerminalObject X S)) :=
  IsTerminal.ofIso (bigSiteIdentityTerminal X S)
    ((relocalizationFunctor_id_iso X S).app (smallTerminalObject X S)).symm

/-- The identity-base relocalization is a morphism of small-to-big pro-étale
sites. -/
instance identity_isMorphismOfSites :
    IsMorphismOfSites (smallTopology X S) (bigTopology X S)
      (relocalizationFunctor (𝟙 S)) := sorry

/-- The inverse image of the identity-base small-to-big site morphism preserves
finite limits. -/
instance identity_sheafPullback_preservesFiniteLimits
    [HasWeakSheafify (bigTopology X S) (Type w)] :
    PreservesFiniteLimits
      ((relocalizationFunctor (𝟙 S)).sheafPullback (Type w)
        (smallTopology X S) (bigTopology X S)) := sorry

/-- The morphism of topoi induced by the identity-base small-to-big pro-étale
site morphism. -/
noncomputable def siteMorphismOfTopoi
    [HasWeakSheafify (bigTopology X S) (Type w)] :
    MorphismOfTopoiIn.{max u v, max u v, v, v, w}
      (smallTopology X S) (bigTopology X S) :=
  Functor.morphismOfTopoiInOfContinuous.{w, max u v, max u v, v, v}
    (relocalizationFunctor (𝟙 S)) (smallTopology X S) (bigTopology X S)

/-- For identity-base pro-étale relocalization, the inverse image of `i_S`
equals the direct image of the induced site morphism `π_S`. -/
theorem morphismOfTopoi_id_inverseImage_eq_siteMorphismOfTopoi_pushforward
    [HasWeakSheafify (bigTopology X S) (Type w)]
    [HasSheafify (smallTopology X S) (Type w)] :
    (morphismOfTopoi (𝟙 S))⁻¹ = (siteMorphismOfTopoi X S).pushforward := sorry

/-- The identity-base small-to-big site morphism is a retraction of the
relocalization morphism of topoi. -/
theorem siteMorphismOfTopoi_comp_morphismOfTopoi_id
    [HasWeakSheafify (bigTopology X S) (Type w)]
    [HasSheafify (smallTopology X S) (Type w)] :
    MorphismOfTopoiIn.comp (siteMorphismOfTopoi X S) (morphismOfTopoi (𝟙 S)) =
      MorphismOfTopoiIn.id (smallTopology X S) := sorry

/-- The direct image of the identity-base site morphism is computed by
evaluation on relocalized small pro-étale objects. -/
theorem siteMorphismOfTopoi_pushforward_obj_obj
    [HasWeakSheafify (bigTopology X S) (Type w)]
    (𝒢 : Sheaf (bigTopology X S) (Type w)) (U : smallSite X S) :
    ((siteMorphismOfTopoi X S).pushforward.obj 𝒢).1.obj (op U) =
      𝒢.1.obj (op ((relocalizationFunctor (𝟙 S)).obj U)) := sorry

end Identity

end SmallToBig
end AlgebraicGeometry.ChosenBigProetaleSite
