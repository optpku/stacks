module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Pullback

/-!
# Small pro-étale adjunction along a closed immersion

If `i : Z ⟶ X` is a closed immersion of schemes, Type-valued inverse image
along `smallProetalePullback i` preserves limits, the corresponding direct
image is fully faithful, and the adjunction counit is an isomorphism.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/-- The counit of `sheafPullback ⊣ sheafPushforwardContinuous` is an isomorphism
on the small pro-étale topos of `Z` when `i` is a closed immersion. -/
instance sheafAdjunction_counit_isIso_of_isClosedImmersion
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [HasSheafify (topology X) (Type (u + 1))]
    [HasSheafify (topology Z) (Type (u + 1))] :
    IsIso ((smallProetalePullback i).sheafAdjunctionContinuous (Type (u + 1))
      (topology X) (topology Z)).counit := sorry

/-- Direct image of Type-valued sheaves along `smallProetalePullback i` is fully
faithful when `i` is a closed immersion. -/
def pushforwardFullyFaithful_of_isClosedImmersion
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [HasSheafify (topology X) (Type (u + 1))]
    [HasSheafify (topology Z) (Type (u + 1))] :
    ((smallProetalePullback i).sheafPushforwardContinuous (Type (u + 1))
      (topology X) (topology Z)).FullyFaithful :=
  ((smallProetalePullback i).sheafAdjunctionContinuous (Type (u + 1))
    (topology X) (topology Z)).fullyFaithfulROfIsIsoCounit

/-- Direct image of Type-valued sheaves along `smallProetalePullback i` is a full
functor when `i` is a closed immersion. -/
instance pushforward_full_of_isClosedImmersion
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [HasSheafify (topology X) (Type (u + 1))]
    [HasSheafify (topology Z) (Type (u + 1))] :
    ((smallProetalePullback i).sheafPushforwardContinuous (Type (u + 1))
      (topology X) (topology Z)).Full :=
  (pushforwardFullyFaithful_of_isClosedImmersion i).full

/-- Direct image of Type-valued sheaves along `smallProetalePullback i` is a
faithful functor when `i` is a closed immersion. -/
instance pushforward_faithful_of_isClosedImmersion
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [HasSheafify (topology X) (Type (u + 1))]
    [HasSheafify (topology Z) (Type (u + 1))] :
    ((smallProetalePullback i).sheafPushforwardContinuous (Type (u + 1))
      (topology X) (topology Z)).Faithful :=
  (pushforwardFullyFaithful_of_isClosedImmersion i).faithful

/-- Inverse image of Type-valued sheaves along `smallProetalePullback i`
preserves limits when `i` is a closed immersion. -/
instance inverseImage_preservesLimits_of_isClosedImmersion
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [HasSheafify (topology X) (Type (u + 1))]
    [HasSheafify (topology Z) (Type (u + 1))] :
    PreservesLimits ((smallProetalePullback i).sheafPullback (Type (u + 1))
      (topology X) (topology Z)) := sorry

/-- The counit isomorphism identifies `sheafPushforwardContinuous ⋙ sheafPullback`
with the identity on Type-valued sheaves on the small pro-étale site of `Z`
when `i` is a closed immersion. -/
def inverseImage_pushforwardIso_of_isClosedImmersion
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [HasSheafify (topology X) (Type (u + 1))]
    [HasSheafify (topology Z) (Type (u + 1))] :
    (smallProetalePullback i).sheafPushforwardContinuous (Type (u + 1))
          (topology X) (topology Z) ⋙
        (smallProetalePullback i).sheafPullback (Type (u + 1))
          (topology X) (topology Z) ≅
      𝟭 (Sheaf (topology Z) (Type (u + 1))) :=
  asIso ((smallProetalePullback i).sheafAdjunctionContinuous (Type (u + 1))
    (topology X) (topology Z)).counit

end AlgebraicGeometry.Scheme.ProEt
