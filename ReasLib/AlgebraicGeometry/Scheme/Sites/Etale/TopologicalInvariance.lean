module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.Equivalence
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.Scheme.AffineEtale

/-- For affine schemes related by a universal homeomorphism, every affine étale object over the source is the pullback of an affine étale object over the target. -/
theorem exists_pullback_iso_of_universalHomeomorphism {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [UniversalHomeomorphism f] (U : X.AffineEtale) :
    ∃ V : Y.AffineEtale,
      Nonempty ((smallEtalePullback f).obj ((AffineEtale.Spec Y).obj V) ≅
        (AffineEtale.Spec X).obj U) := sorry

end AlgebraicGeometry.Scheme.AffineEtale

namespace AlgebraicGeometry.Scheme

/-- For a universal homeomorphism `f : X ⟶ Y`, base change induces an
equivalence from schemes étale over `Y` to schemes étale over `X`. -/
instance smallEtalePullback_isEquivalence_of_universalHomeomorphism
    {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversalHomeomorphism f] :
    (smallEtalePullback f).IsEquivalence := sorry

/-- Base change along a universal homeomorphism preserves and reflects covering
sieves and identifies the small étale sites as dense subsites. -/
instance smallEtalePullback_isDenseSubsite_of_universalHomeomorphism
    {X0 X : Scheme.{u}} (f : X0 ⟶ X) [UniversalHomeomorphism f] :
    Functor.IsDenseSubsite X.smallEtaleTopology X0.smallEtaleTopology
      (smallEtalePullback f) := sorry

/-- Continuous direct image along a universal homeomorphism is an equivalence
of sheaves with values in any coefficient category. -/
instance smallEtaleSheafPushforward_isEquivalence_of_universalHomeomorphism
    (A : Type v) [Category.{w} A]
    {X0 X : Scheme.{u}} (f : X0 ⟶ X) [UniversalHomeomorphism f] :
    ((smallEtalePullback f).sheafPushforwardContinuous A
      X.smallEtaleTopology X0.smallEtaleTopology).IsEquivalence := sorry

/-- Inverse image along a universal homeomorphism is an equivalence of sheaves
with values in any coefficient category. -/
instance smallEtaleSheaf_isEquivalence_of_universalHomeomorphism
    (A : Type v) [Category.{w} A]
    {X0 X : Scheme.{u}} (f : X0 ⟶ X) [UniversalHomeomorphism f] :
    ((smallEtalePullback f).sheafPullback A
      X.smallEtaleTopology X0.smallEtaleTopology).IsEquivalence := sorry

end AlgebraicGeometry.Scheme
