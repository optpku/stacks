/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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

/-- Pulling back an étale object viewed over the target of an open immersion
gives an object isomorphic to the original étale object. -/
theorem openImmersionEtalePullbackIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : X.Etale) :
    Nonempty ((Scheme.smallEtalePullback f).obj (openImmersionEtaleView f U) ≅ U) := sorry

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
