module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.ExactPrecomposition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.HigherDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.ConstantPullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}
variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

/-- Inverse image of an abelian small-étale sheaf along a morphism of schemes. -/
abbrev abelianPullbackAlong {A B : Scheme.{u}} (morphism : A ⟶ B)
    (sheaf : Sheaf B.smallEtaleTopology AddCommGrpCat.{u}) :
    Sheaf A.smallEtaleTopology AddCommGrpCat.{u} :=
  (etaleAbelianSheafPullback morphism).obj sheaf

/-- The continuous direct-image functor for abelian sheaves on small étale sites. -/
abbrev abelianPushforwardAlong {A B : Scheme.{u}} (morphism : A ⟶ B) :
    Sheaf A.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf B.smallEtaleTopology AddCommGrpCat.{u} :=
  (smallEtalePullback morphism).sheafPushforwardContinuous AddCommGrpCat.{u}
    B.smallEtaleTopology A.smallEtaleTopology

/-- Inverse image of abelian small-étale sheaves along a composite is the composite
of the inverse-image functors. -/
def etaleAbelianSheafPullback_comp {A B C : Scheme.{u}}
    (first : B ⟶ A) (second : C ⟶ B) :
    etaleAbelianSheafPullback first ⋙ etaleAbelianSheafPullback second ≅
      etaleAbelianSheafPullback (second ≫ first) :=
  let siteIso : smallEtalePullback first ⋙ smallEtalePullback second ≅
      smallEtalePullback (second ≫ first) :=
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) second first).symm
  Adjunction.leftAdjointCompIso
    ((smallEtalePullback first).sheafAdjunctionContinuous AddCommGrpCat.{u}
      A.smallEtaleTopology B.smallEtaleTopology)
    ((smallEtalePullback second).sheafAdjunctionContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology C.smallEtaleTopology)
    ((smallEtalePullback (second ≫ first)).sheafAdjunctionContinuous AddCommGrpCat.{u}
      A.smallEtaleTopology C.smallEtaleTopology)
    (Functor.sheafPushforwardContinuousComp' siteIso AddCommGrpCat.{u}
      A.smallEtaleTopology B.smallEtaleTopology C.smallEtaleTopology)

/-- A cartesian square of schemes induces the corresponding square of étale
inverse-image functors. -/
def etaleAbelianSheafPullback_square
    (f : X ⟶ Y) {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) :
    etaleAbelianSheafPullback g ⋙ etaleAbelianSheafPullback f' ≅
      etaleAbelianSheafPullback f ⋙ etaleAbelianSheafPullback g' :=
  etaleAbelianSheafPullback_comp g f' ≪≫
    eqToIso (congrArg (fun morphism : X' ⟶ Y ↦ etaleAbelianSheafPullback morphism)
      h_cart.w.symm) ≪≫
    (etaleAbelianSheafPullback_comp f g').symm

/-- The underived base-change mate from inverse image of direct image to
direct image of inverse image. -/
def underivedBaseChange
    (f : X ⟶ Y) {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) :
    abelianPushforwardAlong f ⋙ etaleAbelianSheafPullback g ⟶
      etaleAbelianSheafPullback g' ⋙ abelianPushforwardAlong f' :=
  DerivedBaseChange.map
    ((smallEtalePullback f).sheafAdjunctionContinuous AddCommGrpCat.{u}
      Y.smallEtaleTopology X.smallEtaleTopology)
    ((smallEtalePullback f').sheafAdjunctionContinuous AddCommGrpCat.{u}
      Y'.smallEtaleTopology X'.smallEtaleTopology)
    (etaleAbelianSheafPullback_square f g f' g' h_cart)

/-- The degreewise right-derived component of the underived base-change mate
between the two composite functors. -/
def higherDirectImage_baseChangeHom
    (f : X ⟶ Y) {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    (sheaf : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (degree : ℕ) :
    ((abelianPushforwardAlong f ⋙ etaleAbelianSheafPullback g).rightDerived degree).obj
        sheaf ⟶
      ((etaleAbelianSheafPullback g' ⋙ abelianPushforwardAlong f').rightDerived degree).obj
        sheaf :=
  (NatTrans.rightDerived (underivedBaseChange f g f' g' h_cart) degree).app sheaf

/-- The composite-derived base-change morphism is computed by deriving the
underived base-change natural transformation. -/
theorem higherDirectImage_baseChangeHom_eq
    (f : X ⟶ Y) {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    (sheaf : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (degree : ℕ) :
    higherDirectImage_baseChangeHom f g f' g' h_cart sheaf degree =
      (NatTrans.rightDerived (underivedBaseChange f g f' g' h_cart) degree).app sheaf :=
  rfl

/-- The canonical base-change comparison from inverse image of a higher direct
image to the higher direct image of the inverse-image sheaf. -/
def higherDirectImageBaseChange
    (f : X ⟶ Y) {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    (sheaf : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (degree : ℕ) :
    abelianPullbackAlong g (schemeHigherDirectImage f sheaf degree) ⟶
      schemeHigherDirectImage f' (abelianPullbackAlong g' sheaf) degree :=
  (Functor.RightDerived.postcompObjIso (abelianPushforwardAlong f)
      (etaleAbelianSheafPullback g) degree sheaf).inv ≫
    higherDirectImage_baseChangeHom f g f' g' h_cart sheaf degree ≫
    Functor.RightDerived.precompExactComparisonApp (etaleAbelianSheafPullback g')
      (abelianPushforwardAlong f') degree sheaf

end AlgebraicGeometry.Scheme.Hom

end
