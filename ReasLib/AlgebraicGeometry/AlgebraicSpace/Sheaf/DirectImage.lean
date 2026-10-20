module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.BaseChange
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Small étale pushforward of sheaves on algebraic spaces

The direct image `f_small,*` on sheaves on small étale sites is the composite of
cocontinuous extension along `smallEtaleToSpaces` and continuous evaluation at
`X ×_Y V`. The construction works for any coefficient category admitting the required Kan extensions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Functor CategoryTheory.Limits

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
      (smallEtaleToSpaces X).op.HasPointwiseRightKanExtension P] :
    Sheaf (smallEtaleTopology X) A ⥤ Sheaf (smallEtaleTopology Y) A :=
  (smallEtaleToSpaces X).sheafPushforwardCocontinuous A
      (smallEtaleTopology X) (spacesEtaleTopology X) ⋙
    (etaleBaseChange f).sheafPushforwardContinuous A
      (smallEtaleTopology Y) (spacesEtaleTopology X)

/-- `sheafPushforward` is the composite of cocontinuous extension along `smallEtaleToSpaces`
and continuous pullback along `etaleBaseChange`. -/
theorem sheafPushforward_eq (A : Type v) [Category.{w} A] {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ A,
      (smallEtaleToSpaces X).op.HasPointwiseRightKanExtension P] :
    sheafPushforward A f =
      (smallEtaleToSpaces X).sheafPushforwardCocontinuous A
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
      (smallEtaleToSpaces X).op.HasPointwiseRightKanExtension P] :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} :=
  sheafPushforward AddCommGrpCat.{u + 1} f

/-- The opposite of the small étale inclusion has pointwise right Kan extensions on sheaves of
abelian groups in universe `u + 1`. -/
instance smallEtaleInclusion_op_hasPointwiseRightKanExtension_addCommGrpCat
    (X : AlgebraicSpace S) (P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (smallEtaleToSpaces X).op.HasPointwiseRightKanExtension P :=
  fun _ ↦ inferInstance

/-- Direct image of abelian sheaves is additive. -/
instance sheafPushforward_additive {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (sheafPushforward AddCommGrpCat.{u + 1} f).Additive :=
  sorry

/-- Inverse image of `A`-valued sheaves along a morphism of algebraic spaces, obtained as the
left adjoint composite of sheaf pullback along `etaleBaseChange` and restriction along
`smallEtaleToSpaces`. -/
def sheafInverseImage (A : Type v) [Category.{w} A] {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [∀ F : (smallEtaleSite Y)ᵒᵖ ⥤ A, (etaleBaseChange f).op.HasLeftKanExtension F]
    [HasWeakSheafify (spacesEtaleTopology X) A] :
    Sheaf (smallEtaleTopology Y) A ⥤ Sheaf (smallEtaleTopology X) A :=
  Functor.sheafPullbackConstruction.sheafPullback (etaleBaseChange f) A
      (smallEtaleTopology Y) (spacesEtaleTopology X) ⋙
    (smallEtaleToSpaces X).sheafPushforwardContinuous A
      (smallEtaleTopology X) (spacesEtaleTopology X)

/-- Inverse image is sheaf pullback along `etaleBaseChange` followed by restriction along
`smallEtaleToSpaces`. -/
theorem sheafInverseImage_eq (A : Type v) [Category.{w} A] {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [∀ F : (smallEtaleSite Y)ᵒᵖ ⥤ A, (etaleBaseChange f).op.HasLeftKanExtension F]
    [HasWeakSheafify (spacesEtaleTopology X) A] :
    sheafInverseImage A f =
      Functor.sheafPullbackConstruction.sheafPullback (etaleBaseChange f) A
          (smallEtaleTopology Y) (spacesEtaleTopology X) ⋙
        (smallEtaleToSpaces X).sheafPushforwardContinuous A
          (smallEtaleTopology X) (spacesEtaleTopology X) :=
  rfl

/-- Inverse image of `A`-valued sheaves is left adjoint to small étale pushforward,
as the composite of the Kan-extension adjunction along `etaleBaseChange` and the
cocontinuous adjunction along `smallEtaleToSpaces`. -/
def sheafAdjunction (A : Type v) [Category.{w} A] {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ A,
      (smallEtaleToSpaces X).op.HasPointwiseRightKanExtension P]
    [∀ F : (smallEtaleSite Y)ᵒᵖ ⥤ A, (etaleBaseChange f).op.HasLeftKanExtension F]
    [HasWeakSheafify (spacesEtaleTopology X) A] :
    sheafInverseImage A f ⊣ sheafPushforward A f :=
  (sheafPullbackConstruction.sheafAdjunctionContinuous (etaleBaseChange f) A
      (smallEtaleTopology Y) (spacesEtaleTopology X)).comp
    ((smallEtaleToSpaces X).sheafAdjunctionCocontinuous A
      (smallEtaleTopology X) (spacesEtaleTopology X))

/-- `sheafAdjunction` is the composite of the continuous pullback adjunction along
`etaleBaseChange` with the cocontinuous adjunction along `smallEtaleToSpaces`. -/
theorem sheafAdjunction_eq (A : Type v) [Category.{w} A] {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ A,
      (smallEtaleToSpaces X).op.HasPointwiseRightKanExtension P]
    [∀ F : (smallEtaleSite Y)ᵒᵖ ⥤ A, (etaleBaseChange f).op.HasLeftKanExtension F]
    [HasWeakSheafify (spacesEtaleTopology X) A] :
    sheafAdjunction A f =
      (sheafPullbackConstruction.sheafAdjunctionContinuous (etaleBaseChange f) A
          (smallEtaleTopology Y) (spacesEtaleTopology X)).comp
        ((smallEtaleToSpaces X).sheafAdjunctionCocontinuous A
          (smallEtaleTopology X) (spacesEtaleTopology X)) :=
  rfl

/-- The counit of `sheafAdjunction` is the composite of the two site-level counits. -/
theorem sheafAdjunction_counit_eq (A : Type v) [Category.{w} A] {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ A,
      (smallEtaleToSpaces X).op.HasPointwiseRightKanExtension P]
    [∀ F : (smallEtaleSite Y)ᵒᵖ ⥤ A, (etaleBaseChange f).op.HasLeftKanExtension F]
    [HasWeakSheafify (spacesEtaleTopology X) A]
    (G : Sheaf (smallEtaleTopology X) A) :
    (sheafAdjunction A f).counit.app G =
      ((smallEtaleToSpaces X).sheafPushforwardContinuous A
          (smallEtaleTopology X) (spacesEtaleTopology X)).map
        ((sheafPullbackConstruction.sheafAdjunctionContinuous (etaleBaseChange f) A
            (smallEtaleTopology Y) (spacesEtaleTopology X)).counit.app
          (((smallEtaleToSpaces X).sheafPushforwardCocontinuous A
              (smallEtaleTopology X) (spacesEtaleTopology X)).obj G)) ≫
        ((smallEtaleToSpaces X).sheafAdjunctionCocontinuous A
          (smallEtaleTopology X) (spacesEtaleTopology X)).counit.app G :=
  sorry


/-- Generic direct image is right adjoint to the constructed inverse image,
when the coefficient category supplies the required Kan extension and reflection. -/
instance sheafPushforward_isRightAdjoint (A : Type v) [Category.{w} A]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ A,
      (smallEtaleToSpaces X).op.HasPointwiseRightKanExtension P]
    [∀ P : (smallEtaleSite Y)ᵒᵖ ⥤ A,
      (etaleBaseChange f).op.HasLeftKanExtension P]
    [HasWeakSheafify (spacesEtaleTopology X) A] :
    (sheafPushforward A f).IsRightAdjoint :=
  (sheafAdjunction A f).isRightAdjoint

/-- Upper-universe type presheaves have a genuine pointwise left Kan
extension along the specified base-change functor. -/
instance etaleBaseChange_op_hasLeftKanExtension_type {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (P : (smallEtaleSite Y)ᵒᵖ ⥤ Type (u + 1)) :
    (etaleBaseChange f).op.HasLeftKanExtension P := by
  -- Local instance justification (proof-local temporary data): the actual full comma category fits the coefficient universe u+1.
  letI : (etaleBaseChange f).op.HasPointwiseLeftKanExtension P := fun _ => inferInstance
  exact (Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension
    (etaleBaseChange f).op P).hasLeftKanExtension

/-- The type-valued inverse image uses native upper-universe plus reflection
and the actual base-change Kan construction. -/
def sheafTypeInverseImage {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology Y) (Type (u + 1)) ⥤
      Sheaf (smallEtaleTopology X) (Type (u + 1)) := by
  -- Local instance justification (instance diamond): pin the native plus adjunction rather than the old whole admitted spaces-site reflection.
  letI : HasWeakSheafify (spacesEtaleTopology X) (Type (u + 1)) :=
    (HasSheafify.mk' (spacesEtaleTopology X) (Type (u + 1))
      (plusPlusAdjunction (spacesEtaleTopology X) (Type (u + 1)))).isRightAdjoint
  exact sheafInverseImage (Type (u + 1)) f

/-- Native upper-universe reflection and Kan data give both Hom directions,
unit and counit for type-valued small étale inverse image. -/
def sheafAdjunctionType {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    sheafTypeInverseImage f ⊣ sheafPushforwardType f := by
  -- Local instance justification (instance diamond): use the identical native plus adjunction stored by sheafTypeInverseImage.
  letI : HasWeakSheafify (spacesEtaleTopology X) (Type (u + 1)) :=
    (HasSheafify.mk' (spacesEtaleTopology X) (Type (u + 1))
      (plusPlusAdjunction (spacesEtaleTopology X) (Type (u + 1)))).isRightAdjoint
  exact sheafAdjunction (Type (u + 1)) f

/-- Direct image of type-valued sheaves is right adjoint to inverse image. -/
instance (priority := 1100) sheafPushforwardType_isRightAdjoint {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : (sheafPushforwardType f).IsRightAdjoint :=
  (sheafAdjunctionType f).isRightAdjoint

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
