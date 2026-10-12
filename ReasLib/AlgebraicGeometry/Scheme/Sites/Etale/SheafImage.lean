/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y Z : Scheme.{u}}

/-- Direct image of a Type-valued small-etale sheaf along a morphism of schemes. -/
noncomputable abbrev pushforwardAlong (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    Sheaf Y.smallEtaleTopology (Type (u + 1)) :=
  ((smallEtalePullback f).sheafPushforwardContinuous (Type (u + 1))
      Y.smallEtaleTopology X.smallEtaleTopology).obj F

/-- Inverse image of a Type-valued small-etale sheaf along a morphism of schemes. -/
noncomputable abbrev pullbackAlong (f : X ⟶ Y)
    (G : Sheaf Y.smallEtaleTopology (Type (u + 1))) :
    Sheaf X.smallEtaleTopology (Type (u + 1)) :=
  ((smallEtalePullback f).sheafPullback (Type (u + 1))
      Y.smallEtaleTopology X.smallEtaleTopology).obj G

/-- Inverse image is functorial in the sheaf. -/
noncomputable abbrev pullbackAlongMap (f : X ⟶ Y)
    {G G' : Sheaf Y.smallEtaleTopology (Type (u + 1))} (η : G ⟶ G') :
    pullbackAlong f G ⟶ pullbackAlong f G' :=
  ((smallEtalePullback f).sheafPullback (Type (u + 1))
      Y.smallEtaleTopology X.smallEtaleTopology).map η

/-- The adjunction counit `f⁻¹ f_* F ⟶ F`. -/
noncomputable abbrev counitAlong (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    pullbackAlong f (pushforwardAlong f F) ⟶ F :=
  ((smallEtalePullback f).sheafAdjunctionContinuous (Type (u + 1))
      Y.smallEtaleTopology X.smallEtaleTopology).counit.app F

/-- Site-level identification of successive small-etale pullbacks with pullback along
the composite morphism. -/
noncomputable def pullbackCompSiteIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtalePullback g ⋙ smallEtalePullback f ≅ smallEtalePullback (f ≫ g) :=
  (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g).symm

/-- Direct image along a composite is the composite of the direct images. -/
noncomputable def pushforwardCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    (smallEtalePullback f).sheafPushforwardContinuous (Type (u + 1))
        Y.smallEtaleTopology X.smallEtaleTopology ⋙
      (smallEtalePullback g).sheafPushforwardContinuous (Type (u + 1))
        Z.smallEtaleTopology Y.smallEtaleTopology ≅
      (smallEtalePullback (f ≫ g)).sheafPushforwardContinuous (Type (u + 1))
        Z.smallEtaleTopology X.smallEtaleTopology :=
  Functor.sheafPushforwardContinuousComp' (pullbackCompSiteIso f g) (Type (u + 1))
    Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology

/-- Inverse image along a composite is the composite of the inverse images. -/
noncomputable def pullbackSheafCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    (smallEtalePullback (f ≫ g)).sheafPullback (Type (u + 1))
        Z.smallEtaleTopology X.smallEtaleTopology ≅
      (smallEtalePullback g).sheafPullback (Type (u + 1))
          Z.smallEtaleTopology Y.smallEtaleTopology ⋙
        (smallEtalePullback f).sheafPullback (Type (u + 1))
          Y.smallEtaleTopology X.smallEtaleTopology :=
  (Adjunction.leftAdjointCompIso
    ((smallEtalePullback g).sheafAdjunctionContinuous (Type (u + 1))
      Z.smallEtaleTopology Y.smallEtaleTopology)
    ((smallEtalePullback f).sheafAdjunctionContinuous (Type (u + 1))
      Y.smallEtaleTopology X.smallEtaleTopology)
    ((smallEtalePullback (f ≫ g)).sheafAdjunctionContinuous (Type (u + 1))
      Z.smallEtaleTopology X.smallEtaleTopology)
    (pushforwardCompIso f g)).symm

end AlgebraicGeometry.Scheme.Etale

