module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Whiskering
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose
public import stacks_project.Chap66.Definition_66_18_9_FMap
public import stacks_project.Chap66.Definition_66_29_1_QCoh
public import stacks_project.Chap66.Lemma_66_18_3

/-!
# Pullback of modules on algebraic spaces

A morphism of algebraic spaces induces a morphism of small étale ringed topoi. The associated
module inverse image preserves quasi-coherence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Functor-of-points pullbacks exist in the presheaf category on schemes over `S`. -/
instance : HasPullbacks ((Over S)ᵒᵖ ⥤ Type u) := inferInstance

/-- A morphism of algebraic spaces, viewed as a natural transformation of functors of points. -/
def homFunctor {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    X.functorOfPoints ⟶ Y.functorOfPoints :=
  f

/-- The functor of points of the fibre product of `X` with a scheme étale over `Y`. -/
def etaleBaseChangeFunctorOfPoints {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : smallEtaleSite Y) : (Over S)ᵒᵖ ⥤ Type u :=
  pullback (homFunctor f) (homFunctor V.hom)

/-- The algebraic space `X ×_Y V` obtained by pulling back a scheme étale over `Y`. -/
def etaleBaseChangeSpace {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y) :
    AlgebraicSpace S :=
  ofFunctor (etaleBaseChangeFunctorOfPoints f V) sorry sorry sorry

/-- The first projection of the functor-of-points fibre product. -/
def etaleBaseChangeFst {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y) :
    etaleBaseChangeFunctorOfPoints f V ⟶ X.functorOfPoints :=
  pullback.fst (homFunctor f) (homFunctor V.hom)

/-- The second projection of the functor-of-points fibre product. -/
def etaleBaseChangeSndNat {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y) :
    etaleBaseChangeFunctorOfPoints f V ⟶ (ofOver V.left).functorOfPoints :=
  pullback.snd (homFunctor f) (homFunctor V.hom)

/-- The projection `X ×_Y V ⟶ X`. -/
def etaleBaseChangeHom {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y) :
    etaleBaseChangeSpace f V ⟶ X :=
  etaleBaseChangeFst f V

/-- The projection `X ×_Y V ⟶ V`. -/
def etaleBaseChangeSnd {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y) :
    etaleBaseChangeSpace f V ⟶ ofOver V.left :=
  etaleBaseChangeSndNat f V

/-- Base change of an étale morphism of a scheme along a morphism of algebraic spaces is étale. -/
instance etaleBaseChangeHom_isEtale {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : smallEtaleSite Y) : Etale (etaleBaseChangeHom f V) :=
  sorry

/-- `X ×_Y V` as an object of the étale site of algebraic spaces over `X`. -/
def etaleBaseChangeObj {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y) :
    spacesEtaleSite X :=
  MorphismProperty.Over.mk ⊤ (etaleBaseChangeHom f V) inferInstance

/-- The functor-of-points map `X ×_Y V' ⟶ X ×_Y V` induced by a morphism `V' ⟶ V`. -/
def etaleBaseChangeMapNat {X Y : AlgebraicSpace S} (f : X ⟶ Y) {V V' : smallEtaleSite Y}
    (h : V' ⟶ V) :
    etaleBaseChangeFunctorOfPoints f V' ⟶ etaleBaseChangeFunctorOfPoints f V :=
  pullback.map (homFunctor f) (homFunctor V'.hom) (homFunctor f) (homFunctor V.hom)
    (𝟙 X.functorOfPoints) (homFunctor (ofOverMap h.left)) (𝟙 Y.functorOfPoints) sorry sorry

/-- A morphism of schemes étale over `Y` induces a morphism of fibre products over `X`. -/
def etaleBaseChangeMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) {V V' : smallEtaleSite Y}
    (h : V' ⟶ V) : etaleBaseChangeObj f V' ⟶ etaleBaseChangeObj f V :=
  MorphismProperty.Over.homMk (etaleBaseChangeMapNat f h) sorry

/-- Functoriality of `X ×_Y V` in the scheme étale over `Y`. -/
def etaleBaseChange {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    smallEtaleSite Y ⥤ spacesEtaleSite X where
  obj := etaleBaseChangeObj f
  map h := etaleBaseChangeMap f h
  map_id := sorry
  map_comp := sorry

/-- The object map of `etaleBaseChange f` is the fibre product `X ×_Y V`. -/
theorem etaleBaseChange_obj {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y) :
    (etaleBaseChange f).obj V = etaleBaseChangeObj f V :=
  rfl

/-- Pullback of étale objects along `f` is continuous for the small étale topology of `Y` and the
spaces étale topology of `X`. -/
instance etaleBaseChange_isContinuous {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (etaleBaseChange f).IsContinuous (smallEtaleTopology Y) (spacesEtaleTopology X) :=
  sorry

/-- The small étale inclusion is continuous, as required to present the extension of sheaves as
a morphism of topoi. -/
instance smallEtaleInclusion_isContinuous (X : AlgebraicSpace S) :
    (smallEtaleInclusion X).IsContinuous (smallEtaleTopology X) (spacesEtaleTopology X) :=
  sorry

/-- Ring-valued sheaves on the small étale site of an algebraic space compose with the forgetful
functor to types. -/
instance smallEtaleTopology_hasSheafCompose_forget_ringCat (X : AlgebraicSpace S) :
    (smallEtaleTopology X).HasSheafCompose (forget RingCat.{u}) :=
  sorry

/-- Ring-valued sheaves on the étale site of algebraic spaces over `X` compose with the forgetful
functor to types. -/
instance spacesEtaleTopology_hasSheafCompose_forget_ringCat (X : AlgebraicSpace S) :
    (spacesEtaleTopology X).HasSheafCompose (forget RingCat.{u}) :=
  sorry

/-- Type-valued sheaves in universe `u` on the small étale site of `X` extend along
`smallEtaleInclusion X` by a pointwise right Kan extension. -/
instance smallEtaleInclusion_op_hasPointwiseRightKanExtension_type (X : AlgebraicSpace S)
    (P : (smallEtaleSite X)ᵒᵖ ⥤ Type u) :
    (smallEtaleInclusion X).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Ring-valued sheaves on the small étale site of `X` extend along `smallEtaleInclusion X` by a
pointwise right Kan extension. -/
instance smallEtaleInclusion_op_hasPointwiseRightKanExtension_ringCat (X : AlgebraicSpace S)
    (P : (smallEtaleSite X)ᵒᵖ ⥤ RingCat.{u}) :
    (smallEtaleInclusion X).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Forgetting the ring structure preserves the right Kan extensions that define cocontinuous
direct image along `smallEtaleInclusion X`. -/
instance forget_ringCat_preservesRightKanExtensions_smallEtaleInclusion (X : AlgebraicSpace S) :
    (forget RingCat.{u}).PreservesRightKanExtensions (smallEtaleInclusion X).op :=
  sorry

/-- Ring-valued direct image of the small étale structure sheaf along `f`, obtained by extending
to the spaces étale site and evaluating at `X ×_Y V`. -/
def ringPushforward {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology X) RingCat.{u} ⥤ Sheaf (smallEtaleTopology Y) RingCat.{u} :=
  (smallEtaleInclusion X).sheafPushforwardCocontinuous RingCat.{u}
      (smallEtaleTopology X) (spacesEtaleTopology X) ⋙
    (etaleBaseChange f).sheafPushforwardContinuous RingCat.{u}
      (smallEtaleTopology Y) (spacesEtaleTopology X)

/-- Type-valued direct image along `f`, obtained by extending a small étale sheaf to the spaces
étale site and evaluating at `X ×_Y V`. -/
def typePushforward {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology X) (Type u) ⥤ Sheaf (smallEtaleTopology Y) (Type u) :=
  (smallEtaleInclusion X).sheafPushforwardCocontinuous (Type u)
      (smallEtaleTopology X) (spacesEtaleTopology X) ⋙
    (etaleBaseChange f).sheafPushforwardContinuous (Type u)
      (smallEtaleTopology Y) (spacesEtaleTopology X)

/-- Direct image of type-valued sheaves along `f` is a right adjoint. -/
instance typePushforward_isRightAdjoint {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (typePushforward f).IsRightAdjoint :=
  sorry

/-- Inverse image of type-valued sheaves along `f` is left exact. -/
instance typePushforward_leftAdjoint_preservesFiniteLimits {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : PreservesFiniteLimits (typePushforward f).leftAdjoint :=
  sorry

/-- The morphism of small étale topoi associated to a morphism of algebraic spaces. -/
def morphismOfTopoi {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    MorphismOfTopoiIn (smallEtaleTopology Y) (smallEtaleTopology X) where
  inverseImageFunctor := LeftExactFunctor.of (typePushforward f).leftAdjoint
  pushforward := typePushforward f
  adjunction := Adjunction.ofIsRightAdjoint (typePushforward f)

/-- Forgetting rings commutes with direct image along `f`. -/
def ringPushforwardForgetIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ringPushforward f ⋙ sheafCompose (smallEtaleTopology Y) (forget RingCat.{u}) ≅
      sheafCompose (smallEtaleTopology X) (forget RingCat.{u}) ⋙ typePushforward f :=
  let u := smallEtaleInclusion X
  let v := etaleBaseChange f
  let F := forget RingCat.{u}
  let Ju := smallEtaleTopology X
  let Ku := spacesEtaleTopology X
  let Jv := smallEtaleTopology Y
  (Functor.associator
      (u.sheafPushforwardCocontinuous RingCat.{u} Ju Ku)
      (v.sheafPushforwardContinuous RingCat.{u} Jv Ku)
      (sheafCompose Jv F)) ≪≫
    Functor.isoWhiskerLeft (u.sheafPushforwardCocontinuous RingCat.{u} Ju Ku)
      (eqToIso (Functor.sheafPushforwardContinuous.compSheafCompose v F Jv Ku)) ≪≫
    (Functor.associator
        (u.sheafPushforwardCocontinuous RingCat.{u} Ju Ku)
        (sheafCompose Ku F)
        (v.sheafPushforwardContinuous (Type u) Jv Ku)).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.sheafPushforwardCocontinuous.compSheafComposeIso u F Ju Ku)
      (v.sheafPushforwardContinuous (Type u) Jv Ku) ≪≫
    Functor.associator
      (sheafCompose Ju F)
      (u.sheafPushforwardCocontinuous (Type u) Ju Ku)
      (v.sheafPushforwardContinuous (Type u) Jv Ku)

/-- The component of `f^♯` on an étale square is pullback of global sections along the
underlying scheme morphism. -/
def structureFMap_app {X Y : AlgebraicSpace S} {f : X ⟶ Y} (sq : EtaleSquare f) :
    (structureSheaf Y).obj.obj (op sq.right) ⟶
      (structureSheaf X).obj.obj (op sq.left) :=
  (forget₂ CommRingCat RingCat).map sq.map.left.appTop

/-- The étale square associated to a map from a scheme étale over `X` into `X ×_Y V`. -/
def etaleSquareOfArrow {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y)
    (a : StructuredArrow (op ((etaleBaseChange f).obj V)) (smallEtaleInclusion X).op) :
    EtaleSquare f where
  left := a.right.unop
  right := V
  map :=
    (yonedaEquiv (a.hom.unop.left ≫ etaleBaseChangeSnd f V) : a.right.unop.left ⟶ V.left)
  w := sorry

/-- The cone of `f^♯` components presenting the map `𝒪_Y(V) ⟶ 𝒪_X(X ×_Y V)`. -/
def structureSheafMapCone {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange f).obj V))
        (smallEtaleInclusion X).op ⋙ (structureSheaf X).obj) where
  pt := (structureSheaf Y).obj.obj (op V)
  π :=
    { app := fun a => structureFMap_app (etaleSquareOfArrow f V a)
      naturality := fun _ _ _ => sorry }

/-- The component at `V` of the direct-image structure-sheaf map `𝒪_Y ⟶ f_* 𝒪_X`. -/
def structureSheafMap_app {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : (smallEtaleSite Y)ᵒᵖ) :
    (structureSheaf Y).obj.obj V ⟶
      ((ringPushforward f).obj (structureSheaf X)).obj.obj V :=
  limit.lift _ (structureSheafMapCone f V.unop) ≫
    ((smallEtaleInclusion X).op.ranObjObjIsoLimit (structureSheaf X).obj
        (op ((etaleBaseChange f).obj V.unop))).inv

/-- The direct-image form of `f^♯`, as a morphism of ring sheaves on `Y_étale`. -/
def structureSheafMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    structureSheaf Y ⟶ (ringPushforward f).obj (structureSheaf X) :=
  InducedCategory.homMk
    { app := fun V => structureSheafMap_app f V
      naturality := fun _ _ _ => sorry }

/-- The direct-image structure map is compatible with the canonical internal-ring operations. -/
theorem structureSheafMap_isRingCompatible {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    @RingedSite.ToposHom.Direct.IsRingCompatible (ringedSite X) (ringedSite Y) _ _
      (morphismOfTopoi f) (ringPushforward f) (ringPushforwardForgetIso f)
      (structureSheafMap f) :=
  sorry

/-- The morphism of small étale ringed topoi associated to a morphism of algebraic spaces. -/
def ringedToposHom {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    RingedSite.ToposHom (ringedSite X) (ringedSite Y) :=
  @RingedSite.ToposHom.ofDirectImage (ringedSite X) (ringedSite Y) _ _
    (morphismOfTopoi f) (ringPushforward f) (ringPushforwardForgetIso f)
    (structureSheafMap f) (structureSheafMap_isRingCompatible f)

/-- Restriction of scalars along the inverse-image structure map of `f` is a right adjoint. -/
instance restrictScalars_structureMap_isRightAdjoint {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (SheafOfModules.restrictScalars.{u} (ringedToposHom f).structureMap).IsRightAdjoint :=
  sorry

namespace Modules

/-- The pullback functor `f* : Mod(𝒪_Y) ⟶ Mod(𝒪_X)` of sheaves of modules on the small étale
ringed sites of algebraic spaces. -/
def pullback {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Y.Modules ⥤ X.Modules :=
  (ringedToposHom f).modulePullback

/-- The pullback of modules along a morphism of algebraic spaces is the module pullback of the
associated morphism of ringed topoi. -/
theorem pullback_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    pullback f = (ringedToposHom f).modulePullback :=
  rfl

/-- Quasi-coherence as an object property is preserved by module pullback. -/
theorem pullback_quasiCoherentModuleProperty {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {F : Y.Modules} (hF : quasiCoherentModuleProperty Y F) :
    quasiCoherentModuleProperty X ((pullback f).obj F) :=
  sorry

end Modules

namespace QCoh

/-- Pullback of quasi-coherent modules along a morphism of algebraic spaces. -/
def pullback {X Y : AlgebraicSpace S} (f : X ⟶ Y) : QCoh Y ⥤ QCoh X :=
  ObjectProperty.FullSubcategory.restrict (Modules.pullback f) sorry

/-- The underlying module sheaf of a pulled-back quasi-coherent module is the usual module
pullback. -/
theorem pullback_obj {X Y : AlgebraicSpace S} (f : X ⟶ Y) (F : QCoh Y) :
    ((pullback f).obj F).obj = (Modules.pullback f).obj F.obj :=
  sorry

end QCoh

end AlgebraicGeometry.AlgebraicSpace
