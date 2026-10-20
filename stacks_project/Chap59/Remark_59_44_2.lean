module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.PropertyC

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale.SmallToBig
open scoped MorphismOfTopoiIn

universe u

/- Remark 59.44.2 (1): Property (C) holds for an open immersion. -/
@[stacks 04DU] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.openImmersion_hasPropertyC :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f],
      ∀ (U : X.Etale),
        ∃ (V : Y.Etale) (h : pullback f V.hom ⟶ U.left),
          Surjective h ∧ h ≫ U.hom = pullback.fst f V.hom)

#check (AlgebraicGeometry.Scheme.Etale.SmallToBig.openImmersionEtalePullbackIso :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : X.Etale),
    (Scheme.smallEtalePullback f).obj (openImmersionEtaleView f U) ≅ U)

#check (AlgebraicGeometry.Scheme.Etale.SmallToBig.openImmersionEtalePullbackIso_hom_left :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : X.Etale),
    (openImmersionEtalePullbackIso f U).hom.left =
      pullback.fst ((U.hom : U.left ⟶ X) ≫ f) f)

/- Remark 59.44.2 (2): Property (C) does not force the small direct image
of an open immersion to be an exact functor. -/
@[stacks 04DU] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.openImmersionSmallDirectImage_not_exact :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y),
      IsOpenImmersion f ∧
        ¬ (PreservesFiniteLimits
            ((Scheme.smallEtalePullback f).sheafPushforwardContinuous
              (Type (u + 1)) Y.smallEtaleTopology X.smallEtaleTopology) ∧
          PreservesFiniteColimits
            ((Scheme.smallEtalePullback f).sheafPushforwardContinuous
              (Type (u + 1)) Y.smallEtaleTopology X.smallEtaleTopology)))
