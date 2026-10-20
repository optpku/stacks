module

public import ReasLib.CategoryTheory.Sites.Topos.Morphism
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Monoidal.Internal.Types.CommGrp_
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Grp.Limits

/-! # Abelian sheaves under geometric morphisms -/

set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2000

@[expose] public section

noncomputable section

universe u v u' v' w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace CategoryTheory.MorphismOfTopoiIn

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget AddCommGrpCat.{w})]

private abbrev braiding (J : GrothendieckTopology C) : BraidedCategory (Sheaf J (Type w)) :=
  BraidedCategory.ofCartesianMonoidalCategory

section Comparison

variable [bJ : BraidedCategory (Sheaf J (Type w))]

private abbrev Internal (J : GrothendieckTopology C)
    [bJ : BraidedCategory (Sheaf J (Type w))] :=
  @CommGrp (Sheaf J (Type w)) _ _ bJ

private abbrev underlying (A : Sheaf J AddCommGrpCat.{w}) : Sheaf J (Type w) :=
  (sheafCompose J (forget AddCommGrpCat.{w})).obj A

private def internalOne (A : Sheaf J AddCommGrpCat.{w}) :
    𝟙_ (Sheaf J (Type w)) ⟶ underlying A :=
  ObjectProperty.homMk
    { app := fun V ↦ ↾fun _ ↦ (0 : A.obj.obj V)
      naturality := by intro V W f; ext x; exact ((A.obj.map f).hom.map_zero).symm }

private def internalMul (A : Sheaf J AddCommGrpCat.{w}) :
    underlying A ⊗ underlying A ⟶ underlying A :=
  ObjectProperty.homMk
    { app := fun V ↦ ↾(fun x : A.obj.obj V × A.obj.obj V ↦ x.1 + x.2)
      naturality := by intro V W f; ext x; exact ((A.obj.map f).hom.map_add x.1 x.2).symm }

private def internalInv (A : Sheaf J AddCommGrpCat.{w}) : underlying A ⟶ underlying A :=
  ObjectProperty.homMk
    { app := fun V ↦ ↾(fun x : A.obj.obj V ↦ -x)
      naturality := by intro V W f; ext x; exact ((A.obj.map f).hom.map_neg x).symm }

/-- Pointwise zero, addition, and negation satisfy the internal commutative-group laws. -/
private theorem abelianSheafToInternal_laws (A : Sheaf J AddCommGrpCat.{w}) :
    (internalOne A ▷ underlying A ≫ internalMul A = (λ_ (underlying A)).hom) ∧
    (underlying A ◁ internalOne A ≫ internalMul A = (ρ_ (underlying A)).hom) ∧
    (internalMul A ▷ underlying A ≫ internalMul A =
      (α_ (underlying A) (underlying A) (underlying A)).hom ≫
        underlying A ◁ internalMul A ≫ internalMul A) ∧
    (lift (internalInv A) (𝟙 _) ≫ internalMul A = toUnit _ ≫ internalOne A) ∧
    (lift (𝟙 _) (internalInv A) ≫ internalMul A = toUnit _ ≫ internalOne A) ∧
    ((@BraidedCategory.braiding _ _ _ bJ (underlying A) (underlying A)).hom ≫
      internalMul A = internalMul A) := sorry

@[implicit_reducible]
private def internalGroup (A : Sheaf J AddCommGrpCat.{w}) : GrpObj (underlying A) where
  one := internalOne A
  mul := internalMul A
  inv := internalInv A
  one_mul := (abelianSheafToInternal_laws (bJ := bJ) A).1
  mul_one := (abelianSheafToInternal_laws (bJ := bJ) A).2.1
  mul_assoc := (abelianSheafToInternal_laws (bJ := bJ) A).2.2.1
  left_inv := (abelianSheafToInternal_laws (bJ := bJ) A).2.2.2.1
  right_inv := (abelianSheafToInternal_laws (bJ := bJ) A).2.2.2.2.1

private def toInternalObj (A : Sheaf J AddCommGrpCat.{w}) : Internal J (bJ := bJ) :=
  @CommGrp.mk _ _ _ bJ (underlying A) (internalGroup (bJ := bJ) A)
    (@IsCommMonObj.mk _ _ _ bJ (underlying A) (internalGroup (bJ := bJ) A).toMonObj
      (abelianSheafToInternal_laws (bJ := bJ) A).2.2.2.2.2)

private def toInternalMap {A B : Sheaf J AddCommGrpCat.{w}} (f : A ⟶ B) :
    toInternalObj A ⟶ toInternalObj B :=
  InducedCategory.homMk (Grp.homMk'' ((sheafCompose J (forget AddCommGrpCat.{w})).map f)
    (by ext V x; exact (f.hom.app V).hom.map_zero)
    (by ext V x; exact (f.hom.app V).hom.map_add x.1 x.2))

private def toInternal : Sheaf J AddCommGrpCat.{w} ⥤ Internal J (bJ := bJ) where
  obj := toInternalObj
  map := toInternalMap
  map_id := by intro A; apply CommGrp.hom_ext; rfl
  map_comp := by intro A B D f g; apply CommGrp.hom_ext; rfl

private def evaluationAt (J : GrothendieckTopology C) (V : Cᵒᵖ) :
    Sheaf J (Type w) ⥤ Type w :=
  sheafToPresheaf J (Type w) ⋙ (evaluation Cᵒᵖ (Type w)).obj V

private def sectionFunctor (J : GrothendieckTopology C)
    [bJ : BraidedCategory (Sheaf J (Type w))] (V : Cᵒᵖ) :
    (Internal J (bJ := bJ)) ⥤ AddCommGrpCat.{w} :=
  (@Functor.mapCommGrp (Sheaf J (Type w)) _ _ bJ
    (Type w) _ _ inferInstance (evaluationAt J V)
    (@Functor.Braided.ofChosenFiniteProducts _ _ _ _ _ _ bJ inferInstance
      (evaluationAt J V) (by dsimp [evaluationAt]; infer_instance))) ⋙
    commGrpTypeEquivalenceCommGrp.functor ⋙ commGroupAddCommGroupEquivalence.functor

private def sectionZero (F : Internal J (bJ := bJ)) (V : Cᵒᵖ) : F.X.obj.obj V :=
  @Zero.zero ((sectionFunctor J (bJ := bJ) V).obj F) inferInstance

private def sectionAdd (F : Internal J (bJ := bJ)) (V : Cᵒᵖ)
    (x y : F.X.obj.obj V) : F.X.obj.obj V :=
  @HAdd.hAdd ((sectionFunctor J (bJ := bJ) V).obj F)
    ((sectionFunctor J (bJ := bJ) V).obj F) ((sectionFunctor J (bJ := bJ) V).obj F)
    inferInstance x y

private abbrev reconstructionLaws (J : GrothendieckTopology C)
    [bJ : BraidedCategory (Sheaf J (Type w))] : Prop :=
  (∀ (F : Internal J (bJ := bJ)) {V W : Cᵒᵖ} (g : V ⟶ W),
    (F.X.obj.map g (sectionZero F V) = sectionZero F W) ∧
    ∀ x y : F.X.obj.obj V,
      F.X.obj.map g (sectionAdd F V x y) =
        sectionAdd F W (F.X.obj.map g x) (F.X.obj.map g y)) ∧
  (∀ {F G : Internal J (bJ := bJ)} (α : F ⟶ G) (V : Cᵒᵖ),
    ((CommGrp.forget _).map α).hom.app V (sectionZero F V) = sectionZero G V) ∧
  (∀ {F G : Internal J (bJ := bJ)} (α : F ⟶ G) (V : Cᵒᵖ) (x y : F.X.obj.obj V),
    ((CommGrp.forget _).map α).hom.app V (sectionAdd F V x y) =
      sectionAdd G V (((CommGrp.forget _).map α).hom.app V x)
        (((CommGrp.forget _).map α).hom.app V y))

private def fromPresheaf (h : reconstructionLaws J (bJ := bJ)) (F : Internal J (bJ := bJ)) :
    Cᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj V := (sectionFunctor J (bJ := bJ) V).obj F
  map g := AddCommGrpCat.ofHom
    { toFun := F.X.obj.map g
      map_zero' := (h.1 F g).1
      map_add' := (h.1 F g).2 }
  map_id V := by ext x; exact ConcreteCategory.congr_hom (F.X.obj.map_id V) x
  map_comp g h := by ext x; exact ConcreteCategory.congr_hom (F.X.obj.map_comp g h) x

/-- Evaluation recovers group homomorphisms on restrictions and internal maps, and a sheaf. -/
private theorem abelianSheafFromInternal_laws :
    reconstructionLaws J (bJ := bJ) ∧ ∀ (h : reconstructionLaws J (bJ := bJ)) (F : Internal J (bJ := bJ)),
      Presheaf.IsSheaf J (fromPresheaf h F) := sorry

private def fromInternalObj (F : Internal J (bJ := bJ)) : Sheaf J AddCommGrpCat.{w} :=
  ⟨fromPresheaf abelianSheafFromInternal_laws.1 F,
    abelianSheafFromInternal_laws.2 _ F⟩

private def fromInternalMap {F G : Internal J (bJ := bJ)} (α : F ⟶ G) :
    fromInternalObj F ⟶ fromInternalObj G :=
  ObjectProperty.homMk
    { app := fun V ↦ AddCommGrpCat.ofHom
        { toFun := ((@CommGrp.forget (Sheaf J (Type w)) _ _ bJ).map α).hom.app V
          map_zero' := abelianSheafFromInternal_laws.1.2.1 α V
          map_add' := abelianSheafFromInternal_laws.1.2.2 α V }
      naturality := by
        intro V W g
        ext x
        exact ConcreteCategory.congr_hom (((@CommGrp.forget (Sheaf J (Type w)) _ _ bJ).map α).hom.naturality g) x }

private def fromInternal : (Internal J (bJ := bJ)) ⥤ Sheaf J AddCommGrpCat.{w} where
  obj := fromInternalObj
  map := fromInternalMap
  map_id := by intro F; ext V x; rfl
  map_comp := by intro F G H α β; ext V x; rfl

private def comparisonCounitUnderlying (F : Internal J (bJ := bJ)) :
    (toInternalObj (fromInternalObj F)).X ≅ F.X :=
  ObjectProperty.isoMk _ (Iso.refl F.X.obj)

/-- Reassembling the evaluated groups recovers the original pointwise group operations. -/
private theorem abelianSheafComparison_laws :
    (∀ (A : Sheaf J AddCommGrpCat.{w}) (V : Cᵒᵖ),
    (0 : A.obj.obj V) = (sectionZero (toInternalObj A) V)) ∧
    (∀ (A : Sheaf J AddCommGrpCat.{w}) (V : Cᵒᵖ) (x y : A.obj.obj V),
      (x + y : A.obj.obj V) =
        sectionAdd (toInternalObj A) V x y) ∧
    (∀ F : Internal J (bJ := bJ),
      (toInternalObj (fromInternalObj F)).grp.toMonObj.one ≫
          (comparisonCounitUnderlying F).hom = F.grp.toMonObj.one ∧
      (toInternalObj (fromInternalObj F)).grp.toMonObj.mul ≫
          (comparisonCounitUnderlying F).hom =
        ((comparisonCounitUnderlying F).hom ⊗ₘ (comparisonCounitUnderlying F).hom) ≫
          F.grp.toMonObj.mul) := sorry

private def comparisonUnitApp (A : Sheaf J AddCommGrpCat.{w}) :
    A ≅ fromInternalObj (toInternalObj A) :=
  { hom := ObjectProperty.homMk
      { app := fun V ↦ AddCommGrpCat.ofHom
          { toFun := fun x ↦ x
            map_zero' := abelianSheafComparison_laws.1 A V
            map_add' := abelianSheafComparison_laws.2.1 A V }
        naturality := by intro V W g; ext x; rfl }
    inv := ObjectProperty.homMk
      { app := fun V ↦ AddCommGrpCat.ofHom
          { toFun := fun x ↦ x
            map_zero' := (abelianSheafComparison_laws.1 A V).symm
            map_add' := fun x y ↦ (abelianSheafComparison_laws.2.1 A V x y).symm }
        naturality := by intro V W g; ext x; rfl }
    hom_inv_id := by ext V x; rfl
    inv_hom_id := by ext V x; rfl }

private def comparisonCounitApp (F : Internal J (bJ := bJ)) :
    toInternalObj (fromInternalObj F) ≅ F :=
  CommGrp.mkIso (comparisonCounitUnderlying F)
    (abelianSheafComparison_laws.2.2 F).1 (abelianSheafComparison_laws.2.2 F).2

private def comparison : Sheaf J AddCommGrpCat.{w} ≌ Internal J (bJ := bJ) where
  functor := toInternal
  inverse := fromInternal
  unitIso := NatIso.ofComponents comparisonUnitApp (by intro A B f; ext V x; rfl)
  counitIso := NatIso.ofComponents comparisonCounitApp
    (by intro F G α; apply CommGrp.hom_ext; ext V x; rfl)
  functor_unitIso_comp A := by apply CommGrp.hom_ext; ext V x; rfl

end Comparison

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
variable [K.HasSheafCompose (forget AddCommGrpCat.{w})]

private def mapInternal (F : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    (h : PreservesFiniteProducts F) :
    @CommGrp (Sheaf J (Type w)) _ _ (braiding J) ⥤
      @CommGrp (Sheaf K (Type w)) _ _ (braiding K) :=
  @Functor.mapCommGrp (Sheaf J (Type w)) _ _ (braiding J)
    (Sheaf K (Type w)) _ _ (braiding K) F
    (@Functor.Braided.ofChosenFiniteProducts
      (Sheaf J (Type w)) _ _ (Sheaf K (Type w)) _ _ (braiding J) (braiding K) F h)

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w})] in
private theorem inverseProducts (f : MorphismOfTopoiIn.{u, u', v, v', w} J K) :
    PreservesFiniteProducts f.inverseImage :=
  ⟨fun n ↦ (LeftExactAdjunction.inverseImagePreservesFiniteLimits f).preservesFiniteLimits
    (Discrete (Fin n))⟩

/-- Inverse image on abelian sheaves is the lift of geometric inverse image to internal groups. -/
def abelianInverseImage (f : MorphismOfTopoiIn.{u, u', v, v', w} J K) :
    Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w} :=
  toInternal (bJ := braiding J) ⋙ mapInternal f.inverseImage (inverseProducts f) ⋙
    fromInternal (bJ := braiding K)

/-- Direct image on abelian sheaves is the lift of geometric direct image to internal groups. -/
def abelianDirectImage (f : MorphismOfTopoiIn.{u, u', v, v', w} J K) :
    Sheaf K AddCommGrpCat.{w} ⥤ Sheaf J AddCommGrpCat.{w} :=
  toInternal (bJ := braiding K) ⋙
    mapInternal f.pushforward (LeftExactAdjunction.pushforwardPreservesFiniteProducts f) ⋙
    fromInternal (bJ := braiding J)

private def inverseForgetApp (f : MorphismOfTopoiIn.{u, u', v, v', w} J K)
    (A : Sheaf J AddCommGrpCat.{w}) :
    underlying (f.abelianInverseImage.obj A) ≅ f.inverseImage.obj (underlying A) :=
  ObjectProperty.isoMk _ (Iso.refl _)

private def directForgetApp (f : MorphismOfTopoiIn.{u, u', v, v', w} J K)
    (A : Sheaf K AddCommGrpCat.{w}) :
    underlying (f.abelianDirectImage.obj A) ≅ f.pushforward.obj (underlying A) :=
  ObjectProperty.isoMk _ (Iso.refl _)

/-- The underlying-sheaf inverse-image comparisons are natural. -/
private theorem abelianInverseImage_forget_naturality
    (f : MorphismOfTopoiIn.{u, u', v, v', w} J K)
    {A B : Sheaf J AddCommGrpCat.{w}} (α : A ⟶ B) :
    (sheafCompose K (forget AddCommGrpCat.{w})).map (f.abelianInverseImage.map α) ≫
        (inverseForgetApp f B).hom =
      (inverseForgetApp f A).hom ≫
        f.inverseImage.map ((sheafCompose J (forget AddCommGrpCat.{w})).map α) := sorry

/-- The underlying-sheaf direct-image comparisons are natural. -/
private theorem abelianDirectImage_forget_naturality
    (f : MorphismOfTopoiIn.{u, u', v, v', w} J K)
    {A B : Sheaf K AddCommGrpCat.{w}} (α : A ⟶ B) :
    (sheafCompose J (forget AddCommGrpCat.{w})).map (f.abelianDirectImage.map α) ≫
        (directForgetApp f B).hom =
      (directForgetApp f A).hom ≫
        f.pushforward.map ((sheafCompose K (forget AddCommGrpCat.{w})).map α) := sorry

/-- Forgetting the abelian inverse image recovers geometric inverse image on underlying sheaves. -/
def abelianInverseImageForgetIso (f : MorphismOfTopoiIn.{u, u', v, v', w} J K) :
    f.abelianInverseImage ⋙ sheafCompose K (forget AddCommGrpCat.{w}) ≅
      sheafCompose J (forget AddCommGrpCat.{w}) ⋙ f.inverseImage :=
  NatIso.ofComponents (inverseForgetApp f) (abelianInverseImage_forget_naturality f)

/-- Forgetting the abelian direct image recovers geometric direct image on underlying sheaves. -/
def abelianDirectImageForgetIso (f : MorphismOfTopoiIn.{u, u', v, v', w} J K) :
    f.abelianDirectImage ⋙ sheafCompose J (forget AddCommGrpCat.{w}) ≅
      sheafCompose K (forget AddCommGrpCat.{w}) ⋙ f.pushforward :=
  NatIso.ofComponents (directForgetApp f) (abelianDirectImage_forget_naturality f)

/-- Abelian inverse image is left adjoint to abelian direct image. -/
def abelianAdjunction (f : MorphismOfTopoiIn.{u, u', v, v', w} J K) :
    f.abelianInverseImage ⊣ f.abelianDirectImage :=
  (((comparison (J := J) (bJ := braiding J)).toAdjunction.comp
    (@Adjunction.mapCommGrp (Sheaf J (Type w)) _ _ (braiding J)
      (Sheaf K (Type w)) _ _ (braiding K)
      f.inverseImage f.pushforward f.adjunction
      (@Functor.Braided.ofChosenFiniteProducts
        (Sheaf J (Type w)) _ _ (Sheaf K (Type w)) _ _ (braiding J) (braiding K)
        f.inverseImage (inverseProducts f))
      (@Functor.Braided.ofChosenFiniteProducts
        (Sheaf K (Type w)) _ _ (Sheaf J (Type w)) _ _ (braiding K) (braiding J)
        f.pushforward (LeftExactAdjunction.pushforwardPreservesFiniteProducts f)))).comp
    (comparison (J := K) (bJ := braiding K)).symm.toAdjunction).ofNatIsoLeft
      (Functor.associator (toInternal (bJ := braiding J))
        (mapInternal f.inverseImage (inverseProducts f)) (fromInternal (bJ := braiding K)))

/-- The lifted unit and counit agree with the geometric unit and counit on underlying sheaves. -/
theorem abelianAdjunction_compatibility (f : MorphismOfTopoiIn.{u, u', v, v', w} J K) :
    (∀ A : Sheaf J AddCommGrpCat.{w},
      (sheafCompose J (forget AddCommGrpCat.{w})).map (f.abelianAdjunction.unit.app A) ≫
        (f.abelianDirectImageForgetIso.hom.app (f.abelianInverseImage.obj A)) ≫
        f.pushforward.map (f.abelianInverseImageForgetIso.hom.app A) =
          f.adjunction.unit.app (underlying A)) ∧
    (∀ B : Sheaf K AddCommGrpCat.{w},
      (f.abelianInverseImageForgetIso.hom.app (f.abelianDirectImage.obj B)) ≫
        f.inverseImage.map (f.abelianDirectImageForgetIso.hom.app B) ≫
        f.adjunction.counit.app (underlying B) =
      (sheafCompose K (forget AddCommGrpCat.{w})).map (f.abelianAdjunction.counit.app B)) := sorry

end CategoryTheory.MorphismOfTopoiIn
