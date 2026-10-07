module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.Abelian
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import stacks_project.Chap66.Lemma_66_18_12_Restriction
public import stacks_project.Chap66.Lemma_66_29_2_Pullback

/-!
# Small étale pushforward of sheaves on algebraic spaces

The direct image `f_small,*` on sheaves on small étale sites is the composite of
cocontinuous extension along `smallEtaleInclusion` and continuous evaluation at
`X ×_Y V`. This is the coefficient-polymorphic form of `typePushforward` at the
universe of the étale-site sheaves of section 66.18.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u v w

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImageFunctor`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Direct image of `A`-valued sheaves along a morphism of algebraic spaces, obtained by
extending a small étale sheaf to the spaces étale site and evaluating at `X ×_Y V`. -/
def sheafPushforward (A : Type v) [Category.{w} A] {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ A,
      (smallEtaleInclusion X).op.HasPointwiseRightKanExtension P] :
    Sheaf (smallEtaleTopology X) A ⥤ Sheaf (smallEtaleTopology Y) A :=
  (smallEtaleInclusion X).sheafPushforwardCocontinuous A
      (smallEtaleTopology X) (spacesEtaleTopology X) ⋙
    (etaleBaseChange f).sheafPushforwardContinuous A
      (smallEtaleTopology Y) (spacesEtaleTopology X)

/-- `sheafPushforward` is the composite of cocontinuous extension along `smallEtaleInclusion`
and continuous pullback along `etaleBaseChange`. -/
theorem sheafPushforward_eq (A : Type v) [Category.{w} A] {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ A,
      (smallEtaleInclusion X).op.HasPointwiseRightKanExtension P] :
    sheafPushforward A f =
      (smallEtaleInclusion X).sheafPushforwardCocontinuous A
          (smallEtaleTopology X) (spacesEtaleTopology X) ⋙
        (etaleBaseChange f).sheafPushforwardContinuous A
          (smallEtaleTopology Y) (spacesEtaleTopology X) :=
  rfl

/-- Direct image of type-valued sheaves in universe `u + 1` along a morphism of algebraic
spaces. -/
abbrev sheafPushforwardType {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology X) (Type (u + 1)) ⥤
      Sheaf (smallEtaleTopology Y) (Type (u + 1)) :=
  sheafPushforward (Type (u + 1)) f

/-- Direct image of abelian sheaves along a morphism of algebraic spaces. -/
abbrev sheafPushforwardAbelian {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallEtaleInclusion X).op.HasPointwiseRightKanExtension P] :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} :=
  sheafPushforward AddCommGrpCat.{u + 1} f

/-- The opposite of the small étale inclusion has pointwise right Kan extensions on sheaves of
abelian groups in universe `u + 1`. -/
instance smallEtaleInclusion_op_hasPointwiseRightKanExtension_addCommGrpCat
    (X : AlgebraicSpace S) (P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (smallEtaleInclusion X).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Direct image of sheaves is a right adjoint. -/
instance sheafPushforward_isRightAdjoint (A : Type v) [Category.{w} A]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ A,
      (smallEtaleInclusion X).op.HasPointwiseRightKanExtension P] :
    (sheafPushforward A f).IsRightAdjoint :=
  sorry

/-- Direct image of abelian sheaves is additive. -/
instance sheafPushforward_additive {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (sheafPushforward AddCommGrpCat.{u + 1} f).Additive :=
  sorry

/-- Inverse image of `A`-valued sheaves along a morphism of algebraic spaces, obtained as the
left adjoint composite of sheaf pullback along `etaleBaseChange` and restriction along
`smallEtaleInclusion`. -/
def sheafInverseImage (A : Type v) [Category.{w} A] {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [∀ F : (smallEtaleSite Y)ᵒᵖ ⥤ A, (etaleBaseChange f).op.HasLeftKanExtension F]
    [HasWeakSheafify (spacesEtaleTopology X) A] :
    Sheaf (smallEtaleTopology Y) A ⥤ Sheaf (smallEtaleTopology X) A :=
  Functor.sheafPullbackConstruction.sheafPullback (etaleBaseChange f) A
      (smallEtaleTopology Y) (spacesEtaleTopology X) ⋙
    (smallEtaleInclusion X).sheafPushforwardContinuous A
      (smallEtaleTopology X) (spacesEtaleTopology X)

/-- Inverse image is sheaf pullback along `etaleBaseChange` followed by restriction along
`smallEtaleInclusion`. -/
theorem sheafInverseImage_eq (A : Type v) [Category.{w} A] {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [∀ F : (smallEtaleSite Y)ᵒᵖ ⥤ A, (etaleBaseChange f).op.HasLeftKanExtension F]
    [HasWeakSheafify (spacesEtaleTopology X) A] :
    sheafInverseImage A f =
      Functor.sheafPullbackConstruction.sheafPullback (etaleBaseChange f) A
          (smallEtaleTopology Y) (spacesEtaleTopology X) ⋙
        (smallEtaleInclusion X).sheafPushforwardContinuous A
          (smallEtaleTopology X) (spacesEtaleTopology X) :=
  rfl

/-- The degree-`i` higher direct image functor of abelian sheaves along a morphism of algebraic
spaces. -/
def higherDirectImageFunctor {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [(sheafPushforward AddCommGrpCat.{u + 1} f).Additive]
    (i : ℕ) :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} :=
  (sheafPushforward AddCommGrpCat.{u + 1} f).rightDerived i

/-- The degree-`i` higher direct image of an abelian sheaf along a morphism of algebraic
spaces. -/
def higherDirectImage {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [(sheafPushforward AddCommGrpCat.{u + 1} f).Additive]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (i : ℕ) :
    Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} :=
  (higherDirectImageFunctor f i).obj F

/-- Higher direct image is the object map of `rightDerived` of abelian sheaf pushforward. -/
theorem higherDirectImage_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [(sheafPushforward AddCommGrpCat.{u + 1} f).Additive]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (i : ℕ) :
    higherDirectImage f F i =
      ((sheafPushforward AddCommGrpCat.{u + 1} f).rightDerived i).obj F :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
