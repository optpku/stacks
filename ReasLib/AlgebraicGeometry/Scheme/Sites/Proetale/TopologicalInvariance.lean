module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Topological invariance of the small pro-étale topos

Direct image and inverse image along a universal homeomorphism of schemes
are quasi-inverse equivalences of Type-valued small pro-étale sheaf categories.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/-- Direct image of Type-valued sheaves along a universal homeomorphism is an
equivalence of small pro-étale topoi. -/
instance pushforward_isEquivalence_of_universalHomeomorphism
    {Z X : Scheme.{u}} (i : Z ⟶ X) [UniversalHomeomorphism i] :
    ((smallProetalePullback i).sheafPushforwardContinuous (Type (u + 1))
      (topology X) (topology Z)).IsEquivalence := sorry

/-- Inverse image of Type-valued sheaves along a universal homeomorphism is an
equivalence of small pro-étale topoi. -/
instance inverseImage_isEquivalence_of_universalHomeomorphism
    {Z X : Scheme.{u}} (i : Z ⟶ X) [UniversalHomeomorphism i] :
    ((smallProetalePullback i).sheafPullback (Type (u + 1))
      (topology X) (topology Z)).IsEquivalence :=
  Adjunction.isEquivalence_left_of_isEquivalence_right
    ((smallProetalePullback i).sheafAdjunctionContinuous (Type (u + 1))
      (topology X) (topology Z))

/-- The canonical unit for inverse image and direct image on the small pro-étale
topos is an isomorphism along a universal homeomorphism. -/
instance sheafAdjunction_unit_isIso_of_universalHomeomorphism
    {Z X : Scheme.{u}} (i : Z ⟶ X) [UniversalHomeomorphism i] :
    IsIso ((smallProetalePullback i).sheafAdjunctionContinuous (Type (u + 1))
      (topology X) (topology Z)).unit := by
  infer_instance

/-- The canonical counit for inverse image and direct image on the small pro-étale
topos is an isomorphism along a universal homeomorphism. -/
instance sheafAdjunction_counit_isIso_of_universalHomeomorphism
    {Z X : Scheme.{u}} (i : Z ⟶ X) [UniversalHomeomorphism i] :
    IsIso ((smallProetalePullback i).sheafAdjunctionContinuous (Type (u + 1))
      (topology X) (topology Z)).counit := by
  infer_instance

end AlgebraicGeometry.Scheme.ProEt
