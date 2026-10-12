/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism
public import stacks_project.Chap61.Lemma_61_12_19_Pullback

/-!
# Small pro-étale topos equivalence along a universal homeomorphism

If `i : Z ⟶ X` is a universal homeomorphism of schemes (equivalently an
integral universally injective surjective morphism), the Type-valued small
pro-étale direct image and inverse image are quasi-inverse equivalences.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/-- Direct image of Type-valued sheaves along `smallProetalePullback i` is an
equivalence of small pro-étale topoi when `i` is a universal homeomorphism,
equivalently an integral universally injective surjective morphism. -/
instance pushforward_isEquivalence_of_universalHomeomorphism
    {Z X : Scheme.{u}} (i : Z ⟶ X) [UniversalHomeomorphism i] :
    ((smallProetalePullback i).sheafPushforwardContinuous (Type (u + 1))
      (topology X) (topology Z)).IsEquivalence := sorry

/-- Inverse image of Type-valued sheaves along `smallProetalePullback i` is an
equivalence of small pro-étale topoi when `i` is a universal homeomorphism,
equivalently an integral universally injective surjective morphism. -/
instance inverseImage_isEquivalence_of_universalHomeomorphism
    {Z X : Scheme.{u}} (i : Z ⟶ X) [UniversalHomeomorphism i]
    [HasSheafify (topology X) (Type (u + 1))]
    [HasSheafify (topology Z) (Type (u + 1))] :
    ((smallProetalePullback i).sheafPullback (Type (u + 1))
      (topology X) (topology Z)).IsEquivalence := sorry

/-- The unit of `sheafPullback ⊣ sheafPushforwardContinuous` is an isomorphism
on the small pro-étale topos of `X` when `i` is a universal homeomorphism. -/
instance sheafAdjunction_unit_isIso_of_universalHomeomorphism
    {Z X : Scheme.{u}} (i : Z ⟶ X) [UniversalHomeomorphism i]
    [HasSheafify (topology X) (Type (u + 1))]
    [HasSheafify (topology Z) (Type (u + 1))] :
    IsIso ((smallProetalePullback i).sheafAdjunctionContinuous (Type (u + 1))
      (topology X) (topology Z)).unit := sorry

/-- The counit of `sheafPullback ⊣ sheafPushforwardContinuous` is an isomorphism
on the small pro-étale topos of `Z` when `i` is a universal homeomorphism. -/
instance sheafAdjunction_counit_isIso_of_universalHomeomorphism
    {Z X : Scheme.{u}} (i : Z ⟶ X) [UniversalHomeomorphism i]
    [HasSheafify (topology X) (Type (u + 1))]
    [HasSheafify (topology Z) (Type (u + 1))] :
    IsIso ((smallProetalePullback i).sheafAdjunctionContinuous (Type (u + 1))
      (topology X) (topology Z)).counit := sorry

end AlgebraicGeometry.Scheme.ProEt
