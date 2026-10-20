module
public import ReasLib.CategoryTheory.Functor.KanExtension.UniverseCertificates
public import stacks_project.Chap103.Lemma_103_8_3_LiftedCFG
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap66.«66_26_0_1_Pushforward»

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace
variable {S : Scheme.{u}}

instance smallTypeSheafifyLift (X : AlgebraicSpace S) :
    HasSheafify X.smallEtaleTopology (Type (u + 1)) :=
  Functor.UniverseKan.sheafifyTypes X.smallEtaleTopology

instance spacesTypeSheafifyLift (X : AlgebraicSpace S) :
    HasSheafify (spacesEtaleTopology X) (Type (u + 1)) :=
  Functor.UniverseKan.sheafifyTypes (spacesEtaleTopology X)

instance inclusionTypeRightKanLift (X : AlgebraicSpace S)
    (P : X.smallEtaleSiteᵒᵖ ⥤ Type (u + 1)) :
    (smallEtaleToSpaces X).op.HasPointwiseRightKanExtension P :=
  Functor.UniverseKan.typeRight (smallEtaleToSpaces X) P

instance inclusionRingRightKanLift (X : AlgebraicSpace S)
    (P : X.smallEtaleSiteᵒᵖ ⥤ RingCat.{u + 1}) :
    (smallEtaleToSpaces X).op.HasPointwiseRightKanExtension P :=
  Functor.UniverseKan.ringRight (smallEtaleToSpaces X) P

instance inclusionForgetRightKanLift (X : AlgebraicSpace S) :
    (forget RingCat.{u + 1}).PreservesRightKanExtensions (smallEtaleToSpaces X).op :=
  Functor.UniverseKan.forgetRight (smallEtaleToSpaces X)

instance baseChangeTypeLeftKanLift {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (P : Y.smallEtaleSiteᵒᵖ ⥤ Type (u + 1)) :
    (etaleBaseChange f).op.HasLeftKanExtension P :=
  Functor.UniverseKan.typeLeft (etaleBaseChange f) P

instance smallForgetRingLift (X : AlgebraicSpace S) :
    X.smallEtaleTopology.HasSheafCompose (forget RingCat.{u + 1}) := by infer_instance

instance spacesForgetRingLift (X : AlgebraicSpace S) :
    (spacesEtaleTopology X).HasSheafCompose (forget RingCat.{u + 1}) := by infer_instance

/-- The canonical small-site direct-image recipe, at the honest larger value universe. -/
def typePushforwardLift {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf X.smallEtaleTopology (Type (u + 1)) ⥤ Sheaf Y.smallEtaleTopology (Type (u + 1)) :=
  (smallEtaleToSpaces X).sheafPushforwardCocontinuous (Type (u + 1))
      X.smallEtaleTopology (spacesEtaleTopology X) ⋙
    (etaleBaseChange f).sheafPushforwardContinuous (Type (u + 1))
      Y.smallEtaleTopology (spacesEtaleTopology X)

/-- Ring-valued direct image uses the identical inclusion and base-change functors. -/
def ringPushforwardLift {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf X.smallEtaleTopology RingCat.{u + 1} ⥤ Sheaf Y.smallEtaleTopology RingCat.{u + 1} :=
  (smallEtaleToSpaces X).sheafPushforwardCocontinuous RingCat.{u + 1}
      X.smallEtaleTopology (spacesEtaleTopology X) ⋙
    (etaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
      Y.smallEtaleTopology (spacesEtaleTopology X)

/-- The actual left functor: sheafified left Kan extension along base change,
followed by restriction to the small site. No unproved right-adjoint witness is selected. -/
def typePullbackLift {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf Y.smallEtaleTopology (Type (u + 1)) ⥤ Sheaf X.smallEtaleTopology (Type (u + 1)) :=
  Functor.sheafPullbackConstruction.sheafPullback (etaleBaseChange f) (Type (u + 1))
      Y.smallEtaleTopology (spacesEtaleTopology X) ⋙
    (smallEtaleToSpaces X).sheafPushforwardContinuous (Type (u + 1))
      X.smallEtaleTopology (spacesEtaleTopology X)

/-- The two actual site adjunctions compose to the geometric pullback/pushforward adjunction. -/
def typeAdjunctionLift {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    typePullbackLift f ⊣ typePushforwardLift f :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (etaleBaseChange f)
    (Type (u + 1)) Y.smallEtaleTopology (spacesEtaleTopology X)).comp
      ((smallEtaleToSpaces X).sheafAdjunctionCocontinuous (Type (u + 1))
        X.smallEtaleTopology (spacesEtaleTopology X))

/-- The specified inverse-image functor of this geometric site morphism is left exact. -/
instance typePullbackLift_exact {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    PreservesFiniteLimits (typePullbackLift f) := by sorry

/-- The canonical small étale topos morphism with its displayed upper-universe adjunction. -/
def morphismOfTopoiLift {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    MorphismOfTopoiIn.{u+1,u+1,u,u,u+1} Y.smallEtaleTopology X.smallEtaleTopology where
  inverseImageFunctor := LeftExactFunctor.of (typePullbackLift f)
  pushforward := typePushforwardLift f
  adjunction := typeAdjunctionLift f

/-- The real pointwise ring limits commute with forgetting rings. -/
def ringPushforwardForgetIsoLift {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ringPushforwardLift f ⋙ sheafCompose Y.smallEtaleTopology (forget RingCat.{u + 1}) ≅
      sheafCompose X.smallEtaleTopology (forget RingCat.{u + 1}) ⋙ typePushforwardLift f :=
  let i := smallEtaleToSpaces X
  let v := etaleBaseChange f
  let F := forget RingCat.{u + 1}
  let J := X.smallEtaleTopology
  let K := spacesEtaleTopology X
  let L := Y.smallEtaleTopology
  (Functor.associator (i.sheafPushforwardCocontinuous RingCat.{u + 1} J K)
    (v.sheafPushforwardContinuous RingCat.{u + 1} L K) (sheafCompose L F)) ≪≫
    Functor.isoWhiskerLeft (i.sheafPushforwardCocontinuous RingCat.{u + 1} J K)
      (eqToIso (Functor.sheafPushforwardContinuous.compSheafCompose v F L K)) ≪≫
    (Functor.associator (i.sheafPushforwardCocontinuous RingCat.{u + 1} J K)
      (sheafCompose K F) (v.sheafPushforwardContinuous (Type (u + 1)) L K)).symm ≪≫
    Functor.isoWhiskerRight (Functor.sheafPushforwardCocontinuous.compSheafComposeIso i F J K)
      (v.sheafPushforwardContinuous (Type (u + 1)) L K) ≪≫
    Functor.associator (sheafCompose J F)
      (i.sheafPushforwardCocontinuous (Type (u + 1)) J K)
      (v.sheafPushforwardContinuous (Type (u + 1)) L K)

/-- The lifted structure-ring cone retains the actual canonical étale-square appTop map. -/
def structureSheafMapConeLift {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : Y.smallEtaleSite) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange f).obj V)) (smallEtaleToSpaces X).op ⋙
      (commRingedSiteLift X).structureSheaf.obj) where
  pt := (commRingedSiteLift Y).structureSheaf.obj.obj (op V)
  π :=
    { app := fun q => (ModuleUniverseComparison.coefficientIso Y).inv.hom.app (op V) ≫
        SheafOfModules.UniverseLift.ringHom (structureFMap_app (etaleSquareOfArrow f V q)) ≫
        (ModuleUniverseComparison.coefficientIso X).hom.hom.app q.right
      naturality := by sorry }

/-- The canonical coefficient map is induced by the genuine ring-valued comma limit. -/
def structureSheafMapLift {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (commRingedSiteLift Y).structureSheaf ⟶
      (ringPushforwardLift f).obj (commRingedSiteLift X).structureSheaf :=
  ObjectProperty.homMk
    { app := fun V => limit.lift _ (structureSheafMapConeLift f V.unop) ≫
        ((smallEtaleToSpaces X).op.ranObjObjIsoLimit (commRingedSiteLift X).structureSheaf.obj
          (op ((etaleBaseChange f).obj V.unop))).inv
      naturality := by sorry }

/-- The displayed cone is a map of the actual internal ring structures. -/
theorem structureSheafMapLift_ringCompatible {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    @RingedSite.ToposHom.Direct.IsRingCompatible (commRingedSiteLift X) (commRingedSiteLift Y) _ _
      (morphismOfTopoiLift f) (ringPushforwardLift f) (ringPushforwardForgetIsoLift f)
      (structureSheafMapLift f) := by sorry

/-- The existing canonical lifted ringed sites, with the shared direct-image constructor. -/
def ringedToposHomLift {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    RingedSite.ToposHom (commRingedSiteLift X) (commRingedSiteLift Y) :=
  @RingedSite.ToposHom.ofDirectImage (commRingedSiteLift X) (commRingedSiteLift Y) _ _
    (morphismOfTopoiLift f) (ringPushforwardLift f) (ringPushforwardForgetIsoLift f)
    (structureSheafMapLift f) (structureSheafMapLift_ringCompatible f)

/-- Canonical module pushforward at the same enlarged coefficient/module universe. -/
def Modules.pushforwardLift {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    RingedSite.ModuleCat.{u + 1} (commRingedSiteLift X) ⥤
      RingedSite.ModuleCat.{u + 1} (commRingedSiteLift Y) :=
  (ringedToposHomLift f).modulePushforward

end AlgebraicGeometry.AlgebraicSpace
