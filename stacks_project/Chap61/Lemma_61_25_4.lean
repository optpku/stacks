module

import stacks_project.Chap61.Lemma_61_25_4_Equivalence
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

universe u

/- Lemma 61.25.4 (1): if `i : Z ⟶ X` is an integral universally injective
surjective morphism of schemes (equivalently a universal homeomorphism,
Morphisms Lemma 29.45.5 / 04DF), then the small pro-étale direct image
`(smallProetalePullback i).sheafPushforwardContinuous` is an equivalence of
Type-valued sheaf categories. -/
@[stacks 09AB] #check
  (AlgebraicGeometry.Scheme.ProEt.pushforward_isEquivalence_of_universalHomeomorphism :
    ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [UniversalHomeomorphism i],
      ((smallProetalePullback i).sheafPushforwardContinuous (Type (u + 1))
        (ProEt.topology X) (ProEt.topology Z)).IsEquivalence)

/- Lemma 61.25.4 (2): if `i : Z ⟶ X` is an integral universally injective
surjective morphism of schemes (equivalently a universal homeomorphism,
Morphisms Lemma 29.45.5 / 04DF), then the small pro-étale inverse image
`(smallProetalePullback i).sheafPullback` is an equivalence of Type-valued
sheaf categories, quasi-inverse to the direct image. -/
@[stacks 09AB] #check
  (AlgebraicGeometry.Scheme.ProEt.inverseImage_isEquivalence_of_universalHomeomorphism :
    ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [UniversalHomeomorphism i]
      [HasSheafify (ProEt.topology X) (Type (u + 1))]
      [HasSheafify (ProEt.topology Z) (Type (u + 1))],
      ((smallProetalePullback i).sheafPullback (Type (u + 1))
        (ProEt.topology X) (ProEt.topology Z)).IsEquivalence)

/- The adjunction unit identifies the identity with inverse image followed by
direct image on the small pro-étale topos of `X`. -/
#check
  (AlgebraicGeometry.Scheme.ProEt.sheafAdjunction_unit_isIso_of_universalHomeomorphism :
    ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [UniversalHomeomorphism i]
      [HasSheafify (ProEt.topology X) (Type (u + 1))]
      [HasSheafify (ProEt.topology Z) (Type (u + 1))],
      IsIso ((smallProetalePullback i).sheafAdjunctionContinuous (Type (u + 1))
        (ProEt.topology X) (ProEt.topology Z)).unit)

/- The adjunction counit identifies direct image followed by inverse image
with the identity on the small pro-étale topos of `Z`. -/
#check
  (AlgebraicGeometry.Scheme.ProEt.sheafAdjunction_counit_isIso_of_universalHomeomorphism :
    ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [UniversalHomeomorphism i]
      [HasSheafify (ProEt.topology X) (Type (u + 1))]
      [HasSheafify (ProEt.topology Z) (Type (u + 1))],
      IsIso ((smallProetalePullback i).sheafAdjunctionContinuous (Type (u + 1))
        (ProEt.topology X) (ProEt.topology Z)).counit)
