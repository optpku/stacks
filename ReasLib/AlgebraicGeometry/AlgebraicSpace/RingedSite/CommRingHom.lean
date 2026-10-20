/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
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

/-- Direct image retains commutativity of the input multiplication. -/
theorem commRingPushforward_mul_comm {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (R : Sheaf (smallEtaleTopology X) CommRingCat.{u}) (U : (smallEtaleSite Y)ᵒᵖ)
    (a b : ((ringPushforward f).obj
      ((sheafCompose (smallEtaleTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).obj R)).obj.obj U) :
    a * b = b * a := sorry

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
  map_id := sorry
  map_comp := sorry

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
  sorry

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
     naturality := sorry }⟩

/-- Both ring-composition arrows have the actual small-chart comparison functions. -/
def commRingPushforwardComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    commRingPushforward f ⋙ commRingPushforward g ≅ commRingPushforward (f ≫ g) :=
  NatIso.ofComponents
    (fun R ↦
      { hom := commRingHomOfUnderlying ((commRingPushforwardCompUnderlying f g).hom.app R)
          sorry sorry sorry sorry
        inv := commRingHomOfUnderlying ((commRingPushforwardCompUnderlying f g).inv.app R)
          sorry sorry sorry sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

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

/-- Direct image of commutative-ring sheaves along a morphism of algebraic spaces is a right
adjoint. -/
instance commRingPushforward_isRightAdjoint {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (commRingPushforward f).IsRightAdjoint :=
  sorry

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
      naturality := fun _ _ _ => sorry }

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
      naturality := fun _ _ _ => sorry }

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

/-- Forgetting commutativity of `commInverseImageStructureSheafMap f` recovers the inverse-image
structure map of `ringedToposHom f`. -/
theorem commInverseImageStructureSheafMap_forget {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (sheafCompose (smallEtaleTopology X)
          (forget₂ CommRingCat.{u} RingCat.{u})).map
        (commInverseImageStructureSheafMap f) =
      eqToHom (commInverseImageStructureSheaf_forget f) ≫
        (ringedToposHom f).structureMap ≫
        eqToHom (commStructureSheaf_forget X).symm :=
  sorry

/-- The component of `commInverseImageStructureSheafMap f` forgets to the component of
`(ringedToposHom f).structureMap`. -/
theorem commInverseImageStructureSheafMap_app {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (U : (smallEtaleSite X)ᵒᵖ) :
    (forget₂ CommRingCat.{u} RingCat.{u}).map
        ((commInverseImageStructureSheafMap f).hom.app U) =
      (eqToHom (commInverseImageStructureSheaf_forget f)).hom.app U ≫
        (ringedToposHom f).structureMap.hom.app U ≫
        (eqToHom (commStructureSheaf_forget X).symm).hom.app U :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
