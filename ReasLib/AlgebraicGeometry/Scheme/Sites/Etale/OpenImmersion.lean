module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import Mathlib.CategoryTheory.Limits.ExactFunctor

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MorphismOfTopoiIn

universe u

namespace AlgebraicGeometry.Scheme.Etale.SmallToBig

/-- An étale object over the source of an open immersion is an étale object
over its target by postcomposition with the open immersion. -/
def openImmersionEtaleView {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (U : X.Etale) : Y.Etale :=
  @Scheme.Etale.mk Y U.left ((U.hom : U.left ⟶ X) ≫ f)
    (@AlgebraicGeometry.Etale.etale_comp U.left X
      (U.hom : U.left ⟶ X) Y f U.prop inferInstance)

/-- For an open immersion `f`, the first projection of `U ×_Y X` followed by the
structure map of `U` is the second projection. -/
@[reassoc]
theorem openImmersionEtaleView_pullback_fst_comp
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : X.Etale) :
    pullback.fst ((U.hom : U.left ⟶ X) ≫ f) f ≫ (U.hom : U.left ⟶ X) =
      pullback.snd ((U.hom : U.left ⟶ X) ≫ f) f :=
  (cancel_mono f).mp ((Category.assoc _ _ _).trans pullback.condition)

/-- For an open immersion `f : X ⟶ Y` and `U` étale over `X`, the first projection
`U ×_Y X ⟶ U` is an isomorphism of schemes; its inverse is `(𝟙, U.hom)`. -/
noncomputable def openImmersionEtaleViewPullbackLeftIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : X.Etale) :
    pullback ((U.hom : U.left ⟶ X) ≫ f) f ≅ U.left where
  hom := pullback.fst _ _
  inv := pullback.lift (𝟙 U.left) (U.hom : U.left ⟶ X) (Category.id_comp _)
  hom_inv_id := pullback.hom_ext
    (by simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
        exact Category.comp_id (pullback.fst ((U.hom : U.left ⟶ X) ≫ f) f))
    (by simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
        exact openImmersionEtaleView_pullback_fst_comp f U)
  inv_hom_id := pullback.lift_fst _ _ _

/-- Pulling back an étale object viewed over the target of an open immersion
recovers the original étale object: the canonical identification `U ×_Y X = U`
is given by the first projection. -/
noncomputable def openImmersionEtalePullbackIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : X.Etale) :
    (Scheme.smallEtalePullback f).obj (openImmersionEtaleView f U) ≅ U :=
  MorphismProperty.Over.isoMk (openImmersionEtaleViewPullbackLeftIso f U)
    (openImmersionEtaleView_pullback_fst_comp f U)

/-- The canonical identification `U ×_Y X ≅ U` is the first projection. -/
@[simp]
theorem openImmersionEtalePullbackIso_hom_left
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : X.Etale) :
    (openImmersionEtalePullbackIso f U).hom.left =
      pullback.fst ((U.hom : U.left ⟶ X) ≫ f) f :=
  rfl

/-- There exists an open immersion whose small étale direct image does not
preserve both finite limits and finite colimits. -/
theorem openImmersionSmallDirectImage_not_exact :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y),
      IsOpenImmersion f ∧
        ¬ (PreservesFiniteLimits
            ((Scheme.smallEtalePullback f).sheafPushforwardContinuous
              (Type (u + 1)) Y.smallEtaleTopology X.smallEtaleTopology) ∧
          PreservesFiniteColimits
            ((Scheme.smallEtalePullback f).sheafPushforwardContinuous
              (Type (u + 1)) Y.smallEtaleTopology X.smallEtaleTopology)) := sorry

end AlgebraicGeometry.Scheme.Etale.SmallToBig
