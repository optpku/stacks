module

public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.ExactSquare
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.HigherDirectImage
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Adjunction.Mates

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

namespace HigherDirectImage

variable [∀ {S X : Scheme.{u}} (morphism : X ⟶ S),
    ((smallEtalePullback morphism).sheafPushforwardContinuous AddCommGrpCat.{u}
      S.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]

/-- Inverse image of abelian étale sheaves preserves finite limits. -/
instance inverseImage_preservesFiniteLimits {S X : Scheme.{u}} (morphism : X ⟶ S)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}] :
    PreservesFiniteLimits ((smallEtalePullback morphism).sheafPullback AddCommGrpCat.{u}
      S.smallEtaleTopology X.smallEtaleTopology) := sorry

/-- Inverse image of abelian étale sheaves preserves finite colimits by its adjunction. -/
instance inverseImage_preservesFiniteColimits {S X : Scheme.{u}} (morphism : X ⟶ S) :
    PreservesFiniteColimits ((smallEtalePullback morphism).sheafPullback AddCommGrpCat.{u}
      S.smallEtaleTopology X.smallEtaleTopology) where
  preservesFiniteColimits := fun _ _ _ =>
    ((smallEtalePullback morphism).sheafAdjunctionContinuous AddCommGrpCat.{u}
      S.smallEtaleTopology X.smallEtaleTopology).leftAdjoint_preservesColimits
        |>.preservesColimitsOfShape

/-- Successive inverse images of abelian étale sheaves identify with inverse image
along the composite scheme morphism. -/
def inverseImageCompIso {S X Y : Scheme.{u}} (first : Y ⟶ X) (second : X ⟶ S) :
    (smallEtalePullback second).sheafPullback AddCommGrpCat.{u}
        S.smallEtaleTopology X.smallEtaleTopology ⋙
      (smallEtalePullback first).sheafPullback AddCommGrpCat.{u}
        X.smallEtaleTopology Y.smallEtaleTopology ≅
    (smallEtalePullback (first ≫ second)).sheafPullback AddCommGrpCat.{u}
      S.smallEtaleTopology Y.smallEtaleTopology :=
  let siteIso : smallEtalePullback second ⋙ smallEtalePullback first ≅
      smallEtalePullback (first ≫ second) :=
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) first second).symm
  Adjunction.leftAdjointCompIso
    ((smallEtalePullback second).sheafAdjunctionContinuous AddCommGrpCat.{u}
      S.smallEtaleTopology X.smallEtaleTopology)
    ((smallEtalePullback first).sheafAdjunctionContinuous AddCommGrpCat.{u}
      X.smallEtaleTopology Y.smallEtaleTopology)
    ((smallEtalePullback (first ≫ second)).sheafAdjunctionContinuous AddCommGrpCat.{u}
      S.smallEtaleTopology Y.smallEtaleTopology)
    (Functor.sheafPushforwardContinuousComp'
      siteIso
      AddCommGrpCat.{u} S.smallEtaleTopology X.smallEtaleTopology Y.smallEtaleTopology)

/-- A commutative square of schemes induces ordinary higher-direct-image base change,
without a cartesianness assumption. -/
def baseChange {S X S' X' : Scheme.{u}}
    (vertical : X ⟶ S) (vertical' : X' ⟶ S')
    (top : X' ⟶ X) (bottom : S' ⟶ S)
    (comm : top ≫ vertical = vertical' ≫ bottom)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify S'.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u})]
    (degree : ℕ) :
    ((smallEtalePullback vertical).sheafPushforwardContinuous AddCommGrpCat.{u}
        S.smallEtaleTopology X.smallEtaleTopology).rightDerived degree ⋙
      (smallEtalePullback bottom).sheafPullback AddCommGrpCat.{u}
        S.smallEtaleTopology S'.smallEtaleTopology ⟶
    (smallEtalePullback top).sheafPullback AddCommGrpCat.{u}
        X.smallEtaleTopology X'.smallEtaleTopology ⋙
      ((smallEtalePullback vertical').sheafPushforwardContinuous AddCommGrpCat.{u}
        S'.smallEtaleTopology X'.smallEtaleTopology).rightDerived degree :=
  let inverseSquare := (inverseImageCompIso vertical' bottom) ≪≫
    eqToIso (congrArg
      (fun morphism => (smallEtalePullback morphism).sheafPullback AddCommGrpCat.{u}
        S.smallEtaleTopology X'.smallEtaleTopology) comm.symm) ≪≫
    (inverseImageCompIso top vertical).symm
  let square := (mateEquiv
    (G := (smallEtalePullback bottom).sheafPullback AddCommGrpCat.{u}
      S.smallEtaleTopology S'.smallEtaleTopology)
    (H := (smallEtalePullback top).sheafPullback AddCommGrpCat.{u}
      X.smallEtaleTopology X'.smallEtaleTopology)
    ((smallEtalePullback vertical).sheafAdjunctionContinuous AddCommGrpCat.{u}
      S.smallEtaleTopology X.smallEtaleTopology)
    ((smallEtalePullback vertical').sheafAdjunctionContinuous AddCommGrpCat.{u}
      S'.smallEtaleTopology X'.smallEtaleTopology)) inverseSquare.hom
  Functor.RightDerived.exactSquare _ _ _ _ square.natTrans degree

end HigherDirectImage

end AlgebraicGeometry.Scheme.Etale
