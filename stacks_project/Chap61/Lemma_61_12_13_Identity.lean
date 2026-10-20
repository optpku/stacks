/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation.SmallToBig.Identity

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u v

namespace AlgebraicGeometry.ChosenBigProetaleSite

variable (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier)

/- Lemma 61.12.13 (1): the identity-base relocalization functor defines a morphism
of small-to-big pro-étale sites. -/
#check
  (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.identity_isMorphismOfSites X S :
    IsMorphismOfSites (smallTopology X S) (bigTopology X S)
      (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.relocalizationFunctor (𝟙 S)))

/- Lemma 61.12.13 (2): the identity-base site morphism induces the morphism of
topoi `π_S`. -/
#check
  (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.siteMorphismOfTopoi.{u, v, max u v} X S :
    MorphismOfTopoiIn.{max u v, max u v, u, u, max u v}
      (smallTopology X S) (bigTopology X S))

/- Lemma 61.12.13 (3): the site-induced morphism `π_S` composed with
`i_S = i_{𝟙 S}` has inverse image canonically isomorphic to the identity on the small pro-étale topos. -/
#check
  (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.siteMorphismOfTopoi_comp_morphismOfTopoi_id_iso.{u, v, max u v} X S :
    (MorphismOfTopoiIn.comp
        (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.siteMorphismOfTopoi.{u, v, max u v} X S)
        (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.morphismOfTopoi (𝟙 S)))⁻¹ ≅
      (MorphismOfTopoiIn.id (smallTopology X S))⁻¹)

/- Lemma 61.12.13 (4): the inverse image `i_S⁻¹` equals the direct image
`π_{S,*}`. -/
#check
  (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.morphismOfTopoi_id_inverseImage_eq_siteMorphismOfTopoi_pushforward.{u, v, max u v} X S :
    (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.morphismOfTopoi (𝟙 S))⁻¹ =
      (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.siteMorphismOfTopoi.{u, v, max u v} X S).pushforward)

/- Lemma 61.12.13 (5): the direct image `π_{S,*}` evaluates a big pro-étale sheaf
on the relocalized small pro-étale object. -/
#check
  (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.siteMorphismOfTopoi_pushforward_obj_obj.{u, v, max u v} X S :
    ∀ (𝒢 : Sheaf (bigTopology X S) (Type (max u v))) (U : smallSite X S),
      ((AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.siteMorphismOfTopoi.{u, v, max u v} X S).pushforward.obj 𝒢).1.obj
          (op U) =
        𝒢.1.obj (op ((AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.relocalizationFunctor (𝟙 S)).obj U)))

/- Identity-base relocalization agrees with the full inclusion. -/
#check
  (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.relocalizationFunctor_id_iso X S :
    AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.relocalizationFunctor (𝟙 S) ≅
      smallInclusion X S)

/- Identity-base relocalization is fully faithful. -/
#check
  (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.relocalizationFunctor_id_fullyFaithful X S :
    (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.relocalizationFunctor (𝟙 S)).FullyFaithful)

/- Identity-base relocalization preserves the terminal object. -/
#check
  (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.relocalizationFunctor_id_obj_isTerminal X S :
    IsTerminal ((AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.relocalizationFunctor
      (𝟙 S)).obj (smallTerminalObject X S)))

/- Sheaf pullback along identity-base relocalization preserves finite limits. -/
#check
  (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.identity_sheafPullback_preservesFiniteLimits.{u, v, max u v} X S :
    PreservesFiniteLimits
      ((AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.relocalizationFunctor (𝟙 S)).sheafPullback
        (Type (max u v)) (smallTopology X S) (bigTopology X S)))

end AlgebraicGeometry.ChosenBigProetaleSite
