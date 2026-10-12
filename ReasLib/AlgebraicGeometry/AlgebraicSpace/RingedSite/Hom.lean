/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Whiskering
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Spaces
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose
public import ReasLib.CategoryTheory.Sites.Topos.InternalModule

/-!
# Morphisms of small étale ringed topoi of algebraic spaces

A morphism of algebraic spaces induces a morphism of small étale ringed topoi.
The associated structure-sheaf unit and first higher direct image of `𝒪` are
the comparison maps used to detect contraction of fibres.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open ReasLibPullback
open MorphismProperty

variable {S : Scheme.{u}}

/-- The ring presheaf on the small étale site of `X` with value `Γ(U, 𝒪_U)`. -/
def structurePresheaf (X : AlgebraicSpace S) :
    (smallEtaleSite X)ᵒᵖ ⥤ RingCat.{u} :=
  (smallEtaleToScheme X).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat

/-- The global-sections presheaf on the small étale site of an algebraic space is a sheaf. -/
theorem structurePresheaf_isSheaf (X : AlgebraicSpace S) :
    Presheaf.IsSheaf (smallEtaleTopology X) (structurePresheaf X) :=
  sorry

/-- The structure sheaf `𝒪_X` on the small étale site of an algebraic space. -/
def structureSheaf (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) RingCat.{u} :=
  ⟨structurePresheaf X, structurePresheaf_isSheaf X⟩

/-- The small étale site of `X`, equipped with its structure sheaf. -/
abbrev ringedSite (X : AlgebraicSpace S) : RingedSite.{u + 1, u, u} :=
  RingedSite.ofRingSheaf (smallEtaleTopology X) (structureSheaf X)

/-- The category of sheaves of modules on the ringed site `(X_étale, 𝒪_X)`. -/
abbrev Modules (X : AlgebraicSpace S) :=
  SheafOfModules.{u} (structureSheaf X)

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

/-- Abelian-group-valued sheafification exists on the small étale topology of an algebraic
space. -/
instance smallEtaleTopology_hasSheafify_addCommGrp (X : AlgebraicSpace S) :
    HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u} :=
  sorry

/-- On the small étale topology of an algebraic space, sheafification equivalences are the
locally bijective morphisms. -/
instance smallEtaleTopology_wEqualsLocallyBijective (X : AlgebraicSpace S) :
    (smallEtaleTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  sorry

/-- Injective resolutions exist for module sheaves on the small étale site of an algebraic
space. -/
instance modules_hasInjectiveResolutions (X : AlgebraicSpace S) :
    HasInjectiveResolutions (Modules X) :=
  sorry

/-- The inclusion of schemes étale over `X` into algebraic spaces étale over `X`. -/
def smallEtaleToSpaces (X : AlgebraicSpace S) :
    smallEtaleSite X ⥤ spacesEtaleSite X :=
  SmallEtale.fromPresentation X ⋙ smallEtaleInclusion X

/-- The small-to-spaces comparison is cocontinuous. -/
instance smallEtaleToSpaces_isCocontinuous (X : AlgebraicSpace S) :
    (smallEtaleToSpaces X).IsCocontinuous (smallEtaleTopology X) (spacesEtaleTopology X) :=
  sorry

/-- The small-to-spaces comparison is continuous. -/
instance smallEtaleToSpaces_isContinuous (X : AlgebraicSpace S) :
    (smallEtaleToSpaces X).IsContinuous (smallEtaleTopology X) (spacesEtaleTopology X) :=
  sorry

/-- Type-valued sheaves on the small étale site of `X` extend along `smallEtaleToSpaces X`
by a pointwise right Kan extension. -/
instance smallEtaleToSpaces_op_hasPointwiseRightKanExtension_type (X : AlgebraicSpace S)
    (P : (smallEtaleSite X)ᵒᵖ ⥤ Type u) :
    (smallEtaleToSpaces X).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Ring-valued sheaves on the small étale site of `X` extend along `smallEtaleToSpaces X` by a
pointwise right Kan extension. -/
instance smallEtaleToSpaces_op_hasPointwiseRightKanExtension_ringCat (X : AlgebraicSpace S)
    (P : (smallEtaleSite X)ᵒᵖ ⥤ RingCat.{u}) :
    (smallEtaleToSpaces X).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Forgetting the ring structure preserves the right Kan extensions that define cocontinuous
direct image along `smallEtaleToSpaces X`. -/
instance forget_ringCat_preservesRightKanExtensions_smallEtaleToSpaces (X : AlgebraicSpace S) :
    (forget RingCat.{u}).PreservesRightKanExtensions (smallEtaleToSpaces X).op :=
  sorry

/-- The projection `X ×_Y V ⟶ X` obtained by pulling back a scheme étale over `Y`. -/
def etaleBaseChangeHom {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y) :
    pullback f V.hom ⟶ X :=
  pullback.fst f V.hom

/-- Base change of an étale morphism of a scheme along a morphism of algebraic spaces is étale. -/
instance etaleBaseChangeHom_isEtale {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : smallEtaleSite Y) : Etale (etaleBaseChangeHom f V) :=
  sorry

/-- The projection `X ×_Y V ⟶ V`. -/
def etaleBaseChangeSnd {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y) :
    pullback f V.hom ⟶ ofOver V.left :=
  pullback.snd f V.hom

/-- `X ×_Y V` as an object of the étale site of algebraic spaces over `X`. -/
def etaleBaseChangeObj {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y) :
    spacesEtaleSite X :=
  Over.mk ⊤ (etaleBaseChangeHom f V) inferInstance

/-- The morphism `X ×_Y V' ⟶ X ×_Y V` induced by a morphism `V' ⟶ V`. -/
def etaleBaseChangeMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) {V V' : smallEtaleSite Y}
    (h : V' ⟶ V) : etaleBaseChangeObj f V' ⟶ etaleBaseChangeObj f V :=
  Over.homMk
    (pullback.map f V'.hom f V.hom (𝟙 X) (ofOverMap h.left) (𝟙 Y)
      ((Category.comp_id f).trans (Category.id_comp f).symm) sorry)
    sorry

/-- Functoriality of `X ×_Y V` in the scheme étale over `Y`. -/
def etaleBaseChange {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    smallEtaleSite Y ⥤ spacesEtaleSite X where
  obj := etaleBaseChangeObj f
  map h := etaleBaseChangeMap f h
  map_id := sorry
  map_comp := sorry

/-- Pullback of étale objects along `f` is continuous for the small étale topology of `Y` and the
spaces étale topology of `X`. -/
instance etaleBaseChange_isContinuous {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (etaleBaseChange f).IsContinuous (smallEtaleTopology Y) (spacesEtaleTopology X) :=
  sorry

/-- Ring-valued direct image of the small étale structure sheaf along `f`, obtained by extending
to the spaces étale site and evaluating at `X ×_Y V`. -/
def ringPushforward {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology X) RingCat.{u} ⥤ Sheaf (smallEtaleTopology Y) RingCat.{u} :=
  (smallEtaleToSpaces X).sheafPushforwardCocontinuous RingCat.{u}
      (smallEtaleTopology X) (spacesEtaleTopology X) ⋙
    (etaleBaseChange f).sheafPushforwardContinuous RingCat.{u}
      (smallEtaleTopology Y) (spacesEtaleTopology X)

/-- Type-valued direct image along `f`, obtained by extending a small étale sheaf to the spaces
étale site and evaluating at `X ×_Y V`. -/
def typePushforward {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology X) (Type u) ⥤ Sheaf (smallEtaleTopology Y) (Type u) :=
  (smallEtaleToSpaces X).sheafPushforwardCocontinuous (Type u)
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
  let u := smallEtaleToSpaces X
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

/-- The component of `f^♯` on a morphism of étale charts is pullback of global sections along the
underlying scheme morphism. -/
def structureFMap_app {X Y : AlgebraicSpace S} {U : smallEtaleSite X}
    {V : smallEtaleSite Y} (h : U.left ⟶ V.left) :
    (structureSheaf Y).obj.obj (op V) ⟶
      (structureSheaf X).obj.obj (op U) :=
  (forget₂ CommRingCat RingCat).map h.left.appTop

/-- The scheme morphism over `S` associated to a map from a scheme étale over `X` into
`X ×_Y V`. -/
def schemeMapOfArrow {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y)
    (a : StructuredArrow (op ((etaleBaseChange f).obj V)) (smallEtaleToSpaces X).op) :
    a.right.unop.left ⟶ V.left :=
  yonedaEquiv (a.hom.unop.left ≫ etaleBaseChangeSnd f V)

/-- The cone of `f^♯` components presenting the map `𝒪_Y(V) ⟶ 𝒪_X(X ×_Y V)`. -/
def structureSheafMapCone {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange f).obj V))
        (smallEtaleToSpaces X).op ⋙ (structureSheaf X).obj) where
  pt := (structureSheaf Y).obj.obj (op V)
  π :=
    { app := fun a => structureFMap_app (schemeMapOfArrow f V a)
      naturality := fun _ _ _ => sorry }

/-- The component at `V` of the direct-image structure-sheaf map `𝒪_Y ⟶ f_* 𝒪_X`. -/
def structureSheafMap_app {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : (smallEtaleSite Y)ᵒᵖ) :
    (structureSheaf Y).obj.obj V ⟶
      ((ringPushforward f).obj (structureSheaf X)).obj.obj V :=
  limit.lift _ (structureSheafMapCone f V.unop) ≫
    ((smallEtaleToSpaces X).op.ranObjObjIsoLimit (structureSheaf X).obj
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

/-- The type-valued sheaf underlying the structure module `𝒪_X` compares with the
underlying structure sheaf of the small étale ringed site. -/
def unitUnderlyingIso (X : AlgebraicSpace S) :
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj
      (SheafOfModules.unit (structureSheaf X)) ≅
      RingedSite.Hom.underlyingStructureSheaf (ringedSite X) :=
  Iso.refl _

namespace Modules

/-- The canonical morphism `𝒪_Y ⟶ f_* 𝒪_X` of `𝒪_Y`-modules associated to a
morphism of algebraic spaces. -/
def unitToPushforwardObjUnit {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    SheafOfModules.unit (structureSheaf Y) ⟶
      (ringedToposHom f).modulePushforward.obj (SheafOfModules.unit (structureSheaf X)) :=
  Sheaf.InternalModule.homOfUnderlying (structureSheaf Y)
    ((unitUnderlyingIso Y).hom ≫
      (ringedToposHom f).underlyingDirectImageMap ≫
      (ringedToposHom f).toTopos.pushforward.map (unitUnderlyingIso X).inv ≫
      (RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom f)).inv.app
        (SheafOfModules.unit (structureSheaf X)))
    sorry sorry

end Modules

/-- The first higher direct image `R¹ f_* 𝒪_X` of the structure sheaf. -/
def higherDirectImageOne {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Modules Y :=
  (@Functor.rightDerived _ _ _ _ _ _ _ (ringedToposHom f).modulePushforward
      (RingedSite.ToposHom.modulePushforward_additive (ringedToposHom f)) 1).obj
    (SheafOfModules.unit (structureSheaf X))

end AlgebraicGeometry.AlgebraicSpace
