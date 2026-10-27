/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.RingTheory.FreeRing
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Sites.Point.Map
public import ReasLib.Algebra.Category.CommRing.Sheaf.Internal
public import ReasLib.Algebra.Category.Ring.Sheaf.LocalHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationInclusion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRing

/-!
# Inverse-image structure maps of morphisms of algebraic spaces

A morphism of algebraic spaces induces a commutative-ring valued inverse-image form of
`f^♯` on small étale sites.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Sheaf.InternalCommRing
open CategoryTheory.Sheaf.InternalRing

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Inverse image of type-valued sheaves along a morphism of algebraic spaces preserves finite
products. -/
instance morphismOfTopoi_inverseImage_preservesFiniteProducts {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : PreservesFiniteProducts (morphismOfTopoi f).inverseImage :=
  inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- Direct image retains commutativity of the input multiplication. -/
theorem commRingPushforward_mul_comm {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (R : Sheaf (smallEtaleTopology X) CommRingCat.{u}) (U : (smallEtaleSite Y)ᵒᵖ)
    (a b : ((ringPushforward f).obj
      ((sheafCompose (smallEtaleTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).obj R)).obj.obj U) :
    a * b = b * a := by
  letI : BraidedCategory (Sheaf (smallEtaleTopology X) (Type u)) :=
    sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology X)
  letI : BraidedCategory (Sheaf (smallEtaleTopology Y) (Type u)) :=
    sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology Y)
  let A : RingObjects.{u + 1, u, u} (smallEtaleTopology X) :=
    CategoryTheory.Sheaf.InternalCommRing.ToInternal.ringObject.{u + 1, u, u} R
  let F := (morphismOfTopoi f).pushforward
  letI : MonObj A.X := A.ringObj.toMonObj
  letI : IsCommMonObj A.X := by
    constructor
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    apply ConcreteCategory.hom_ext
    intro p
    exact @mul_comm (R.obj.obj V) _ p.2 p.1
  letI : PreservesFiniteProducts F :=
    LeftExactAdjunction.pushforwardPreservesFiniteProducts (morphismOfTopoi f)
  letI : F.Braided := Functor.Braided.ofChosenFiniteProducts F
  letI : MonObj (F.obj A.X) := Functor.mapRingMonObj F A
  have h := @IsCommMonObj.mul_comm _ _ _ _ (F.obj A.X) _
    (Functor.isCommMonObj_obj (F := F))
  exact congrArg (fun k ↦ k.hom.app U (b, a)) h

/-- The commutative view keeps all section carriers and operations of the actual ring direct image. -/
def commRingPushforwardObj {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (R : Sheaf (smallEtaleTopology X) CommRingCat.{u}) :
    Sheaf (smallEtaleTopology Y) CommRingCat.{u} :=
  let Q := (ringPushforward f).obj
    ((sheafCompose (smallEtaleTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  ⟨SheafOfModules.TensorScalarExtension.commView Q.obj (commRingPushforward_mul_comm f R), by
    apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ CommRingCat.{u} RingCat.{u})
    exact Q.property⟩

/-- Commutative-ring direct image uses the same small-chart section maps as ring direct image. -/
def commRingPushforward {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} ⥤
      Sheaf (smallEtaleTopology Y) CommRingCat.{u} where
  obj := commRingPushforwardObj f
  map {R T} g := ⟨SheafOfModules.TensorScalarExtension.commMap
    ((ringPushforward f).map
      ((sheafCompose (smallEtaleTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map g)).hom
    (commRingPushforward_mul_comm f R) (commRingPushforward_mul_comm f T)⟩
  map_id R := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply CommRingCat.hom_ext
    exact congrArg (fun α ↦ (α.hom.app U).hom)
      ((sheafCompose (smallEtaleTopology X) (forget₂ CommRingCat.{u} RingCat.{u}) ⋙
        ringPushforward f).map_id R)
  map_comp α β := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply CommRingCat.hom_ext
    exact congrArg (fun γ ↦ (γ.hom.app U).hom)
      ((sheafCompose (smallEtaleTopology X) (forget₂ CommRingCat.{u} RingCat.{u}) ⋙
        ringPushforward f).map_comp α β)

/-- The direct-image object is the commutative view of the specified ring direct image. -/
theorem commRingPushforward_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (R : Sheaf (smallEtaleTopology X) CommRingCat.{u}) :
    (commRingPushforward f).obj R = commRingPushforwardObj f R :=
  rfl

/-- Commutative-ring-valued sheaves on the étale site of algebraic spaces over `X` compose with
the forgetful functor to rings. -/
instance spacesEtaleTopology_hasSheafCompose_commRing (X : AlgebraicSpace S) :
    (spacesEtaleTopology X).HasSheafCompose
      (forget₂ CommRingCat.{u} RingCat.{u}) :=
  by
    let e : coyoneda.obj (op (RingCat.of (FreeRing PUnit.{u + 1}))) ≅
        forget RingCat.{u} :=
      NatIso.ofComponents (fun R ↦ Equiv.toIso
        { toFun := fun α ↦ α.hom (FreeRing.of PUnit.unit)
          invFun := fun r ↦ RingCat.ofHom (FreeRing.lift (fun _ ↦ r))
          left_inv := fun α ↦ by
            apply RingCat.hom_ext
            apply FreeRing.hom_ext
            intro x
            cases x
            exact FreeRing.lift_of _ _
          right_inv := fun r ↦ FreeRing.lift_of _ _ })
        (fun α ↦ by ext g; rfl)
    letI : PreservesLimitsOfSize.{u + 1, u + 1} (forget RingCat.{u}) :=
      preservesLimits_of_natIso e
    letI : ReflectsLimitsOfSize.{u + 1, u + 1} (forget RingCat.{u}) :=
      { reflectsLimitsOfShape :=
          { reflectsLimit := fun {D} ↦
              { reflects := fun {c} hc ↦ by
                  letI : HasLimit (D ⋙ forget RingCat.{u}) := ⟨_, hc⟩
                  letI : Small.{u} (D ⋙ forget RingCat.{u}).sections :=
                    (Types.hasLimit_iff_small_sections _).mp inferInstance
                  exact (reflectsLimit_of_reflectsIsomorphisms D
                    (forget RingCat.{u})).reflects hc } } }
    letI : PreservesLimitsOfSize.{u + 1, u + 1}
        (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget RingCat.{u}) :=
      inferInstanceAs (PreservesLimitsOfSize.{u + 1, u + 1} (forget CommRingCat.{u}))
    letI : PreservesLimitsOfSize.{u + 1, u + 1} (forget₂ CommRingCat.{u} RingCat.{u}) :=
      preservesLimits_of_reflects_of_preserves _ (forget RingCat.{u})
    exact hasSheafCompose_of_preservesLimitsOfSize (spacesEtaleTopology X)

/-- Forgetting commutativity commutes with `commRingPushforward`. -/
def commRingPushforwardForgetIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    commRingPushforward f ⋙
        sheafCompose (smallEtaleTopology Y) (forget₂ CommRingCat.{u} RingCat.{u}) ≅
      sheafCompose (smallEtaleTopology X) (forget₂ CommRingCat.{u} RingCat.{u}) ⋙
        ringPushforward f :=
  Iso.refl _

/-- Forget both commutativity and ring operations, retaining the underlying section types. -/
def commRingUnderlying (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} ⥤ Sheaf (smallEtaleTopology X) (Type u) :=
  sheafCompose (smallEtaleTopology X) (forget₂ CommRingCat.{u} RingCat.{u}) ⋙
    sheafCompose (smallEtaleTopology X) (forget RingCat.{u})

/-- Underlying direct-image types are the specified small-chart direct image. -/
def commRingPushforwardUnderlyingIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    commRingPushforward f ⋙ commRingUnderlying Y ≅ commRingUnderlying X ⋙ typePushforward f :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (commRingPushforwardForgetIso f)
      (sheafCompose (smallEtaleTopology Y) (forget RingCat.{u})) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (sheafCompose (smallEtaleTopology X) (forget₂ CommRingCat.{u} RingCat.{u}))
      (ringPushforwardForgetIso f) ≪≫ (Functor.associator _ _ _).symm

/-- Underlying types of an iterated commutative-ring direct image. -/
def commRingPushforwardIteratedIso {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (commRingPushforward f ⋙ commRingPushforward g) ⋙ commRingUnderlying Z ≅
      commRingUnderlying X ⋙ typePushforward f ⋙ typePushforward g :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (commRingPushforward f) (commRingPushforwardUnderlyingIso g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (commRingPushforwardUnderlyingIso f) (typePushforward g) ≪≫
    Functor.associator _ _ _

/-- Actual type-valued comparison for composition of commutative-ring direct images. -/
def commRingPushforwardCompUnderlying {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (commRingPushforward f ⋙ commRingPushforward g) ⋙ commRingUnderlying Z ≅
      commRingPushforward (f ≫ g) ⋙ commRingUnderlying Z :=
  commRingPushforwardIteratedIso f g ≪≫
    Functor.isoWhiskerLeft (commRingUnderlying X) (Modules.typePushforwardComp f g) ≪≫
    (commRingPushforwardUnderlyingIso (f ≫ g)).symm

/-- Equip a specified underlying section map with its commutative-ring homomorphism laws. -/
def commRingHomOfUnderlying {X : AlgebraicSpace S}
    {R T : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (α : (commRingUnderlying X).obj R ⟶ (commRingUnderlying X).obj T)
    (h0 : ∀ U, α.hom.app U (0 : R.obj.obj U) = (0 : T.obj.obj U))
    (h1 : ∀ U, α.hom.app U (1 : R.obj.obj U) = (1 : T.obj.obj U))
    (hadd : ∀ U (r s : R.obj.obj U), α.hom.app U (r + s) =
      ((inferInstance : Add (T.obj.obj U)).add (α.hom.app U r) (α.hom.app U s) : T.obj.obj U))
    (hmul : ∀ U (r s : R.obj.obj U), α.hom.app U (r * s) =
      ((inferInstance : Mul (T.obj.obj U)).mul (α.hom.app U r) (α.hom.app U s) : T.obj.obj U)) :
    R ⟶ T :=
  ⟨{ app := fun U ↦ CommRingCat.ofHom
      { toFun := α.hom.app U
        map_zero' := h0 U
        map_one' := h1 U
        map_add' := hadd U
        map_mul' := hmul U }
     naturality := fun {U V} g ↦ by
       apply CommRingCat.hom_ext
       apply RingHom.ext
       intro r
       exact congrArg (fun k ↦ k r) (α.hom.naturality g) }⟩

/-- Both ring-composition arrows have the actual small-chart comparison functions. -/
def commRingPushforwardComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    commRingPushforward f ⋙ commRingPushforward g ≅ commRingPushforward (f ≫ g) :=
  NatIso.ofComponents
    (fun R ↦
      { hom := commRingHomOfUnderlying ((commRingPushforwardCompUnderlying f g).hom.app R)
          sorry sorry sorry sorry
        inv := commRingHomOfUnderlying ((commRingPushforwardCompUnderlying f g).inv.app R)
          sorry sorry sorry sorry
        hom_inv_id := by
          apply Sheaf.hom_ext
          apply NatTrans.ext
          funext U
          apply CommRingCat.hom_ext
          apply RingHom.ext
          intro r
          exact congrArg (fun k ↦ k.hom.app U r)
            (((commRingPushforwardCompUnderlying f g).app R).hom_inv_id)
        inv_hom_id := by
          apply Sheaf.hom_ext
          apply NatTrans.ext
          funext U
          apply CommRingCat.hom_ext
          apply RingHom.ext
          intro r
          exact congrArg (fun k ↦ k.hom.app U r)
            (((commRingPushforwardCompUnderlying f g).app R).inv_hom_id) })
    (fun {R T} α ↦ by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro r
      exact congrArg (fun k ↦ k.hom.app U r)
        ((commRingPushforwardCompUnderlying f g).hom.naturality α))

/-- Evaluate commutative-ring direct image along the specified scheme chart of its fibre product. -/
def commRingPushforwardEvaluation {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (R : Sheaf (smallEtaleTopology X) CommRingCat.{u}) {V : smallEtaleSite Y} {U : smallEtaleSite X}
    (a : (smallEtaleToSpaces X).obj U ⟶ (etaleBaseChange f).obj V) :
    ((commRingPushforward f).obj R).obj.obj (op V) ⟶ R.obj.obj (op U) :=
  @CommRingCat.ofHom (((commRingPushforward f).obj R).obj.obj (op V)) (R.obj.obj (op U))
    (inferInstanceAs (CommRing (((commRingPushforward f).obj R).obj.obj (op V))))
    (inferInstanceAs (CommRing (R.obj.obj (op U))))
    { toFun := fun r ↦ EtaleTopos.extensionEvaluation X ((commRingUnderlying X).obj R) a
        (((commRingPushforwardUnderlyingIso f).hom.app R).hom.app (op V) r)
      map_zero' := sorry
      map_one' := sorry
      map_add' := sorry
      map_mul' := sorry }

/-- Forgetting commutativity after `commRingPushforward` recovers `ringPushforward`. -/
theorem commRingPushforward_forget {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    commRingPushforward f ⋙
        sheafCompose (smallEtaleTopology Y) (forget₂ CommRingCat.{u} RingCat.{u}) =
      sheafCompose (smallEtaleTopology X) (forget₂ CommRingCat.{u} RingCat.{u}) ⋙
        ringPushforward f :=
  rfl

set_option maxHeartbeats 800000 in
/-- Direct image of commutative-ring sheaves along a morphism of algebraic spaces is a right
adjoint. -/
instance commRingPushforward_isRightAdjoint {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (commRingPushforward f).IsRightAdjoint :=
  (((CategoryTheory.Sheaf.InternalCommRing.equivalence.{u + 1, u, u}
      (J := smallEtaleTopology Y)).toAdjunction.comp
      (@Functor.mapCommRingOfFiniteProductsAdjunction
        (Sheaf (smallEtaleTopology Y) (Type u)) _ _
        (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology Y))
        (Sheaf (smallEtaleTopology X) (Type u)) _ _
        (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology X))
        (morphismOfTopoi f).inverseImage inferInstance
        (morphismOfTopoi f).pushforward
        (LeftExactAdjunction.pushforwardPreservesFiniteProducts (morphismOfTopoi f))
        (morphismOfTopoi f).adjunction)).comp
    (CategoryTheory.Sheaf.InternalCommRing.equivalence.{u + 1, u, u}
      (J := smallEtaleTopology X)).symm.toAdjunction).isRightAdjoint

/-- The component of `f^♯` on an étale square, retained as a morphism of commutative rings. -/
def commStructureFMap_app {X Y : AlgebraicSpace S} {f : X ⟶ Y} (sq : EtaleSquare f) :
    (commStructureSheaf Y).obj.obj (op sq.right) ⟶
      (commStructureSheaf X).obj.obj (op sq.left) :=
  sq.map.left.appTop

/-- Forgetting commutativity of `commStructureFMap_app` recovers `structureFMap_app`. -/
theorem commStructureFMap_app_forget {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (sq : EtaleSquare f) :
    (forget₂ CommRingCat RingCat).map (commStructureFMap_app sq) = structureFMap_app sq :=
  rfl

/-- The cone of commutative `f^♯` components presenting `𝒪_Y(V) ⟶ 𝒪_X(X ×_Y V)`. -/
def commStructureSheafMapCone {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange f).obj V))
        (smallEtaleToSpaces X).op ⋙ (commStructureSheaf X).obj) where
  pt := (commStructureSheaf Y).obj.obj (op V)
  π :=
    { app := fun a => commStructureFMap_app (etaleSquareOfArrow f V a)
      naturality := fun {a b} g ↦ by
        apply CommRingCat.hom_ext
        exact congrArg (fun α ↦ α.hom)
          ((structureSheafMapCone f V).π.naturality g) }

/-- The component at `V` of the commutative direct-image structure-sheaf map. -/
def commStructureSheafMap_app {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : (smallEtaleSite Y)ᵒᵖ) :
    (commStructureSheaf Y).obj.obj V ⟶
      ((commRingPushforward f).obj (commStructureSheaf X)).obj.obj V :=
  @CommRingCat.ofHom ((commStructureSheaf Y).obj.obj V)
    (((commRingPushforward f).obj (commStructureSheaf X)).obj.obj V)
    (inferInstanceAs (CommRing ((commStructureSheaf Y).obj.obj V)))
    (inferInstanceAs (CommRing (((commRingPushforward f).obj (commStructureSheaf X)).obj.obj V)))
    (structureSheafMap_app f V).hom

/-- The direct-image form of `f^♯` as a morphism of commutative-ring sheaves on `Y_étale`. -/
def commStructureSheafMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    commStructureSheaf Y ⟶ (commRingPushforward f).obj (commStructureSheaf X) :=
  InducedCategory.homMk
    { app := fun V => commStructureSheafMap_app f V
      naturality := fun {U V} g ↦ by
        apply CommRingCat.hom_ext
        exact congrArg (fun α ↦ α.hom) ((structureSheafMap f).hom.naturality g) }

/-- The component of `commStructureSheafMap` at `V` is `commStructureSheafMap_app`. -/
theorem commStructureSheafMap_app_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : (smallEtaleSite Y)ᵒᵖ) :
    (commStructureSheafMap f).hom.app V = commStructureSheafMap_app f V :=
  rfl

/-- Inverse image of internal commutative rings along the morphism of small étale topoi
associated to `f`. -/
def internalCommRingInverseImage {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    CommRingObjects (smallEtaleTopology Y) ⥤ CommRingObjects (smallEtaleTopology X) :=
  @Functor.mapCommRingOfFiniteProducts
    (Sheaf (smallEtaleTopology Y) (Type u)) _ _
    (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology Y))
    (Sheaf (smallEtaleTopology X) (Type u)) _ _
    (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology X))
    (morphismOfTopoi f).inverseImage inferInstance

/-- Forgetting commutativity after internal inverse image recovers ring-level inverse image. -/
def internalCommRingInverseImage_forgetRingIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    internalCommRingInverseImage f ⋙
        CommRingObjects.forgetRing (smallEtaleTopology X) ≅
      CommRingObjects.forgetRing (smallEtaleTopology Y) ⋙
        (morphismOfTopoi f).internalRingInverseImage :=
  @Functor.mapCommRingOfFiniteProductsForgetRingIso
    (Sheaf (smallEtaleTopology Y) (Type u)) _ _
    (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology Y))
    (Sheaf (smallEtaleTopology X) (Type u)) _ _
    (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology X))
    (morphismOfTopoi f).inverseImage inferInstance

/-- Internal inverse image of commutative rings forgets to internal inverse image of rings. -/
theorem internalCommRingInverseImage_forgetRing {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (R : CommRingObjects (smallEtaleTopology Y)) :
    (CommRingObjects.forgetRing (smallEtaleTopology X)).obj
        ((internalCommRingInverseImage f).obj R) =
      (morphismOfTopoi f).internalRingInverseImage.obj
        ((CommRingObjects.forgetRing (smallEtaleTopology Y)).obj R) :=
  rfl

/-- The inverse-image commutative structure sheaf `f⁻¹𝒪_Y` on `X_étale`. -/
def commInverseImageStructureSheaf {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} :=
  fromInternalObj.{u + 1, u, u}
    ((internalCommRingInverseImage f).obj
      (toInternalObj.{u + 1, u, u} (commStructureSheaf Y)))

/-- Forgetting commutativity of `commStructureSheaf X` recovers `structureSheaf X`. -/
theorem commStructureSheaf_forget (X : AlgebraicSpace S) :
    (sheafCompose (smallEtaleTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (commStructureSheaf X) =
      structureSheaf X :=
  rfl

/-- Forgetting commutativity of `commInverseImageStructureSheaf f` recovers the ring-valued
inverse image of `𝒪_Y`. -/
theorem commInverseImageStructureSheaf_forget {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (sheafCompose (smallEtaleTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (commInverseImageStructureSheaf f) =
      (morphismOfTopoi f).ringInverseImage.obj (structureSheaf Y) :=
  rfl

/-- The type-valued direct-image form of the underlying map of `commStructureSheafMap`. -/
def commStructureSheafMap_underlying {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (sheafCompose (smallEtaleTopology Y) (forget RingCat.{u})).obj
        ((sheafCompose (smallEtaleTopology Y)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj (commStructureSheaf Y)) ⟶
      (morphismOfTopoi f).pushforward.obj
        ((sheafCompose (smallEtaleTopology X) (forget RingCat.{u})).obj
          ((sheafCompose (smallEtaleTopology X)
              (forget₂ CommRingCat.{u} RingCat.{u})).obj (commStructureSheaf X))) :=
  (sheafCompose (smallEtaleTopology Y) (forget RingCat.{u})).map
      ((sheafCompose (smallEtaleTopology Y)
          (forget₂ CommRingCat.{u} RingCat.{u})).map (commStructureSheafMap f)) ≫
    (sheafCompose (smallEtaleTopology Y) (forget RingCat.{u})).map
      ((commRingPushforwardForgetIso f).hom.app (commStructureSheaf X)) ≫
    (ringPushforwardForgetIso f).hom.app
      ((sheafCompose (smallEtaleTopology X)
          (forget₂ CommRingCat.{u} RingCat.{u})).obj (commStructureSheaf X))

/-- `commStructureSheafMap_underlying` is the type-valued transport of `commStructureSheafMap`. -/
theorem commStructureSheafMap_underlying_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    commStructureSheafMap_underlying f =
      (sheafCompose (smallEtaleTopology Y) (forget RingCat.{u})).map
          ((sheafCompose (smallEtaleTopology Y)
              (forget₂ CommRingCat.{u} RingCat.{u})).map (commStructureSheafMap f)) ≫
        (sheafCompose (smallEtaleTopology Y) (forget RingCat.{u})).map
          ((commRingPushforwardForgetIso f).hom.app (commStructureSheaf X)) ≫
        (ringPushforwardForgetIso f).hom.app
          ((sheafCompose (smallEtaleTopology X)
              (forget₂ CommRingCat.{u} RingCat.{u})).obj (commStructureSheaf X)) :=
  rfl

/-- The inverse-image form of `f^♯` as a morphism of commutative-ring sheaves on `X_étale`. -/
def commInverseImageStructureSheafMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    commInverseImageStructureSheaf f ⟶ commStructureSheaf X :=
  CategoryTheory.Sheaf.InternalCommRing.fromInternalMap
      (@CommRingObjCat.Hom.mk (Sheaf (smallEtaleTopology X) (Type u)) _ _
        (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology X))
        ((internalCommRingInverseImage f).obj
          (toInternalObj.{u + 1, u, u} (commStructureSheaf Y)))
        (toInternalObj.{u + 1, u, u} (commStructureSheaf X))
        (((morphismOfTopoi f).adjunction.homEquiv
            (CommRingObjects.carrier (smallEtaleTopology Y)
              (toInternalObj.{u + 1, u, u} (commStructureSheaf Y)))
            (CommRingObjects.carrier (smallEtaleTopology X)
              (toInternalObj.{u + 1, u, u} (commStructureSheaf X)))).symm
          (commStructureSheafMap_underlying f))
        sorry) ≫
    (CategoryTheory.Sheaf.InternalCommRing.toFromIso.{u + 1, u, u}).hom.app
      (commStructureSheaf X)

set_option backward.isDefEq.respectTransparency false in
/-- Forgetting commutativity of `commInverseImageStructureSheafMap f` recovers the inverse-image
structure map of `ringedToposHom f`. -/
theorem commInverseImageStructureSheafMap_forget {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (sheafCompose (smallEtaleTopology X)
          (forget₂ CommRingCat.{u} RingCat.{u})).map
        (commInverseImageStructureSheafMap f) =
      eqToHom (commInverseImageStructureSheaf_forget f) ≫
        (ringedToposHom f).structureMap ≫
        eqToHom (commStructureSheaf_forget X).symm :=
  by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply RingCat.hom_ext
    apply RingHom.ext
    intro r
    dsimp only [commInverseImageStructureSheafMap, ringedToposHom,
      EtaleRingedTopos.ringedHom, RingedSite.ToposHom.ofDirectImage,
      RingedSite.ToposHom.Direct.inverseStructureMap,
      RingedSite.ToposHom.Direct.inverseMap, MorphismOfTopoiIn.internalRingAdjunction,
      Functor.mapRingOfFiniteProductsAdjunction, Functor.mapRingAdjunction]
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    rfl

/-- The component of `commInverseImageStructureSheafMap f` forgets to the component of
`(ringedToposHom f).structureMap`. -/
theorem commInverseImageStructureSheafMap_app {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (U : (smallEtaleSite X)ᵒᵖ) :
    (forget₂ CommRingCat.{u} RingCat.{u}).map
        ((commInverseImageStructureSheafMap f).hom.app U) =
      (eqToHom (commInverseImageStructureSheaf_forget f)).hom.app U ≫
        (ringedToposHom f).structureMap.hom.app U ≫
        (eqToHom (commStructureSheaf_forget X).symm).hom.app U :=
  by
    exact congrArg (fun α ↦ α.hom.app U) (commInverseImageStructureSheafMap_forget f)

end AlgebraicGeometry.AlgebraicSpace
