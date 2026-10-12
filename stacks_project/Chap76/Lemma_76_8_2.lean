/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap66.Lemma_66_18_6_Site
public import stacks_project.Chap66.Lemma_66_18_8_Representable
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap76.Theorem_76_8_1_Equivalence

/-!
# Restriction of the spaces-étale equivalence to small and affine étale sites

Under the hypotheses of Theorem 76.8.1, base change along `f` restricts to
equivalences of small étale sites and of affine étale sites.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An integral morphism of algebraic spaces is relatively representable. -/
theorem IsIntegralHom.relativelyRepresentable {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsIntegralHom f] : yoneda.relativelyRepresentable f :=
  sorry

/-- An object of the spaces-étale site of `Y` is a scheme if and only if its
base change along `f` is a scheme. -/
theorem spacesEtalePullback.obj_isScheme_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f] [Surjective f]
    (V : spacesEtaleSite Y) :
    IsScheme ((spacesEtalePullback f).obj V).left ↔ IsScheme V.left :=
  sorry

/-- An object of the spaces-étale site of `Y` is affine if and only if its
base change along `f` is affine. -/
theorem spacesEtalePullback.obj_isAffine_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f] [Surjective f]
    (V : spacesEtaleSite Y) :
    IsAffine ((spacesEtalePullback f).obj V).left ↔ IsAffine V.left :=
  sorry

/-- Lemma 76.8.2 (1): with the assumptions of Theorem 76.8.1, base change along
`f` restricts to an equivalence `smallEtaleSite Y ⥤ smallEtaleSite X`. -/
@[stacks 07VW, instance]
instance smallEtalePullback.isEquivalence {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f] [Surjective f]
    (hf : yoneda.relativelyRepresentable f) :
    (smallEtalePullback f hf).IsEquivalence :=
  sorry

/-- Base change along an integral morphism sends affine objects of the small
étale site of `Y` to affine objects of the small étale site of `X`. -/
theorem affineEtaleObjects.map_smallEtalePullback {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f]
    (hf : yoneda.relativelyRepresentable f) (U : affineEtaleSite Y) :
    affineEtaleObjects X ((affineEtaleInclusion Y ⋙ smallEtalePullback f hf).obj U) :=
  sorry

/-- Base change along an integral morphism as a functor of affine étale sites. -/
def affineEtalePullback {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIntegralHom f] (hf : yoneda.relativelyRepresentable f) :
    affineEtaleSite Y ⥤ affineEtaleSite X :=
  (affineEtaleObjects X).lift (affineEtaleInclusion Y ⋙ smallEtalePullback f hf)
    (affineEtaleObjects.map_smallEtalePullback f hf)

/-- Affine étale pullback sits over small étale pullback via the inclusions. -/
def affineEtalePullback.comp_inclusion {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsIntegralHom f] (hf : yoneda.relativelyRepresentable f) :
    affineEtalePullback f hf ⋙ affineEtaleInclusion X ≅
      affineEtaleInclusion Y ⋙ smallEtalePullback f hf :=
  (affineEtaleObjects X).liftCompιIso (affineEtaleInclusion Y ⋙ smallEtalePullback f hf)
    (affineEtaleObjects.map_smallEtalePullback f hf)

/-- Lemma 76.8.2 (2): with the assumptions of Theorem 76.8.1, base change along
`f` restricts to an equivalence `affineEtaleSite Y ⥤ affineEtaleSite X`. -/
@[stacks 07VW, instance]
instance affineEtalePullback.isEquivalence {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f] [Surjective f]
    (hf : yoneda.relativelyRepresentable f) :
    (affineEtalePullback f hf).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
