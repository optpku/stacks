module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Sites.Point.Map
public import ReasLib.Algebra.Category.CommRing.Sheaf.Internal
public import ReasLib.Algebra.Category.Ring.Sheaf.LocalHom
public import stacks_project.Chap66.Definition_66_19_1_GeometricPoint
public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing
public import stacks_project.Chap66.Lemma_66_18_3
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap66.Lemma_66_29_7_CommSheaf

/-!
# Inverse-image structure maps of morphisms of algebraic spaces

A morphism of algebraic spaces induces a commutative-ring valued inverse-image form of
`f^♯` on small étale sites.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Sheaf.InternalCommRing
open CategoryTheory.Sheaf.InternalRing
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The opposite of the small étale inclusion has pointwise right Kan extensions on
commutative-ring-valued presheaves. -/
instance smallEtaleInclusion_op_hasPointwiseRightKanExtension_commRingCat
    (X : AlgebraicSpace S) (P : (smallEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u}) :
    (smallEtaleInclusion X).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Inverse image of type-valued sheaves along a morphism of algebraic spaces preserves finite
products. -/
instance morphismOfTopoi_inverseImage_preservesFiniteProducts {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : PreservesFiniteProducts (morphismOfTopoi f).inverseImage :=
  inferInstance

/-- Commutative-ring-valued direct image along a morphism of algebraic spaces, obtained by
extending a small étale sheaf to the spaces étale site and evaluating at `X ×_Y V`. -/
def commRingPushforward {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} ⥤
      Sheaf (smallEtaleTopology Y) CommRingCat.{u} :=
  (smallEtaleInclusion X).sheafPushforwardCocontinuous CommRingCat.{u}
      (smallEtaleTopology X) (spacesEtaleTopology X) ⋙
    (etaleBaseChange f).sheafPushforwardContinuous CommRingCat.{u}
      (smallEtaleTopology Y) (spacesEtaleTopology X)

/-- `commRingPushforward` is the commutative-ring parallel of `ringPushforward`. -/
theorem commRingPushforward_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    commRingPushforward f =
      (smallEtaleInclusion X).sheafPushforwardCocontinuous CommRingCat.{u}
          (smallEtaleTopology X) (spacesEtaleTopology X) ⋙
        (etaleBaseChange f).sheafPushforwardContinuous CommRingCat.{u}
          (smallEtaleTopology Y) (spacesEtaleTopology X) :=
  rfl

/-- Commutative-ring-valued sheaves on the étale site of algebraic spaces over `X` compose with
the forgetful functor to rings. -/
instance spacesEtaleTopology_hasSheafCompose_commRing (X : AlgebraicSpace S) :
    (spacesEtaleTopology X).HasSheafCompose
      (forget₂ CommRingCat.{u} RingCat.{u}) :=
  sorry

/-- Forgetting commutativity preserves the right Kan extensions that define cocontinuous
direct image along `smallEtaleInclusion X`. -/
instance forget₂_commRingCat_preservesRightKanExtensions_smallEtaleInclusion
    (X : AlgebraicSpace S) :
    (forget₂ CommRingCat.{u} RingCat.{u}).PreservesRightKanExtensions
      (smallEtaleInclusion X).op :=
  sorry

/-- Forgetting commutativity commutes with `commRingPushforward`. -/
def commRingPushforwardForgetIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    commRingPushforward f ⋙
        sheafCompose (smallEtaleTopology Y) (forget₂ CommRingCat.{u} RingCat.{u}) ≅
      sheafCompose (smallEtaleTopology X) (forget₂ CommRingCat.{u} RingCat.{u}) ⋙
        ringPushforward f :=
  let u := smallEtaleInclusion X
  let v := etaleBaseChange f
  let F := forget₂ CommRingCat.{u} RingCat.{u}
  let Ju := smallEtaleTopology X
  let Ku := spacesEtaleTopology X
  let Jv := smallEtaleTopology Y
  (Functor.associator
      (u.sheafPushforwardCocontinuous CommRingCat.{u} Ju Ku)
      (v.sheafPushforwardContinuous CommRingCat.{u} Jv Ku)
      (sheafCompose Jv F)) ≪≫
    Functor.isoWhiskerLeft (u.sheafPushforwardCocontinuous CommRingCat.{u} Ju Ku)
      (eqToIso (Functor.sheafPushforwardContinuous.compSheafCompose v F Jv Ku)) ≪≫
    (Functor.associator
        (u.sheafPushforwardCocontinuous CommRingCat.{u} Ju Ku)
        (sheafCompose Ku F)
        (v.sheafPushforwardContinuous RingCat.{u} Jv Ku)).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.sheafPushforwardCocontinuous.compSheafComposeIso u F Ju Ku)
      (v.sheafPushforwardContinuous RingCat.{u} Jv Ku) ≪≫
    Functor.associator
      (sheafCompose Ju F)
      (u.sheafPushforwardCocontinuous RingCat.{u} Ju Ku)
      (v.sheafPushforwardContinuous RingCat.{u} Jv Ku)

/-- Forgetting commutativity after `commRingPushforward` recovers `ringPushforward`. -/
theorem commRingPushforward_forget {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    commRingPushforward f ⋙
        sheafCompose (smallEtaleTopology Y) (forget₂ CommRingCat.{u} RingCat.{u}) =
      sheafCompose (smallEtaleTopology X) (forget₂ CommRingCat.{u} RingCat.{u}) ⋙
        ringPushforward f :=
  sorry

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
        (smallEtaleInclusion X).op ⋙ (commStructureSheaf X).obj) where
  pt := (commStructureSheaf Y).obj.obj (op V)
  π :=
    { app := fun a => commStructureFMap_app (etaleSquareOfArrow f V a)
      naturality := fun _ _ _ => sorry }

/-- The component at `V` of the commutative direct-image structure-sheaf map. -/
def commStructureSheafMap_app {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : (smallEtaleSite Y)ᵒᵖ) :
    (commStructureSheaf Y).obj.obj V ⟶
      ((commRingPushforward f).obj (commStructureSheaf X)).obj.obj V :=
  limit.lift _ (commStructureSheafMapCone f V.unop) ≫
    ((smallEtaleInclusion X).op.ranObjObjIsoLimit (commStructureSheaf X).obj
        (op ((etaleBaseChange f).obj V.unop))).inv

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
  sorry

/-- Forgetting commutativity of `commInverseImageStructureSheaf f` recovers the ring-valued
inverse image of `𝒪_Y`. -/
theorem commInverseImageStructureSheaf_forget {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (sheafCompose (smallEtaleTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (commInverseImageStructureSheaf f) =
      (morphismOfTopoi f).ringInverseImage.obj (structureSheaf Y) :=
  sorry

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