module

public import Mathlib.CategoryTheory.Sites.Pullback
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap67.Lemma_67_14_1_Quotient
public import stacks_project.Chap67.Lemma_67_28_12_IdealSheaf
public import stacks_project.Chap67.Remark_67_12_4_Coborder
public import stacks_project.Chap76.Definition_76_7_2_Differentials
public import stacks_project.Chap76.Lemma_76_9_2_Structure
public import stacks_project.Chap79.«79_5_1_1_Infinitesimal»

/-!
# Parameters of infinitesimal source sections

A global `𝒪_{U₀}`-module map `θ : e₀^* Ω_{R₀/U₀} ⟶ 𝒞_{U₀/U}` perturbs the
identity section of a groupoid in algebraic spaces, yielding a unique
infinitesimal source section `δ = θ · e`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace hiding Hom
open AlgebraicGeometry.AlgebraicSpace.Thickening
open scoped AlgebraicGeometry.AlgebraicSpace
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}}

/-- The conormal sheaf `𝒞_{Z/X}` of an immersion, as `I / I²` pulled back along
the coborder closed immersion. -/
abbrev thickeningConormal {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [AlgebraicSpace.IsImmersion i] : Z.Modules :=
  (Modules.pullback (AlgebraicSpace.IsImmersion.liftCoborder i)).obj
    (Modules.quotientByIdeal
      (AlgebraicSpace.Hom.idealSheafSubobject (AlgebraicSpace.IsImmersion.liftCoborder i))
      (AlgebraicSpace.Hom.idealSheaf (AlgebraicSpace.IsImmersion.liftCoborder i)))

/-- `thickeningConormal i` is the coborder ideal quotient pulled back to `Z`. -/
theorem thickeningConormal_eq {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [AlgebraicSpace.IsImmersion i] :
    thickeningConormal i =
      (Modules.pullback (AlgebraicSpace.IsImmersion.liftCoborder i)).obj
        (Modules.quotientByIdeal
          (AlgebraicSpace.Hom.idealSheafSubobject (AlgebraicSpace.IsImmersion.liftCoborder i))
          (AlgebraicSpace.Hom.idealSheaf (AlgebraicSpace.IsImmersion.liftCoborder i))) := rfl

variable {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
variable {U₀ : AlgebraicSpace S} (ι : U₀ ⟶ G.U.left)

/-- A parameter is a global `𝒪_{U₀}`-linear map
`e₀^* Ω[s₀] ⟶ Hom.conormalSheaf ι`. The codomain `thickeningConormal ι` is
definitionally the coborder formula of `AlgebraicSpace.Hom.conormalSheaf`;
that declaration cannot be imported together with `Ω[f]` because both
introduce `commRingPushforward`. -/
abbrev Parameter [IsFirstOrderThickening ι] :=
  (Modules.pullback (identityRestrict G ι)).obj Ω[sourceRestrict G ι] ⟶
    thickeningConormal ι

/-- Unfolding of `Parameter`. -/
theorem Parameter_eq [IsFirstOrderThickening ι] :
    Parameter G ι =
      ((Modules.pullback (identityRestrict G ι)).obj Ω[sourceRestrict G ι] ⟶
        thickeningConormal ι) := rfl

/-- The `s₀`-derivation into `e₀_* 𝒞_{U₀/U}` associated to a parameter `θ`. -/
def derivationOfParameter [IsFirstOrderThickening ι] (θ : Parameter G ι) :
    AlgebraicSpace.Hom.derivations (sourceRestrict G ι)
      ((Modules.pushforward (identityRestrict G ι)).obj (thickeningConormal ι)) :=
  (d[sourceRestrict G ι]).postcomp
    ((SheafOfModules.forget (structureSheaf (arrowRestrict G ι)) ⋙
        PresheafOfModules.restrictScalars
          (𝟙 (structureSheaf (arrowRestrict G ι)).obj)).map
      ((Modules.pullbackPushforwardAdjunction (identityRestrict G ι)).homEquiv _ _ θ))

/-- `derivationOfParameter θ` is `d[s₀].postcomp` of the adjunct of `θ`. -/
theorem derivationOfParameter_eq [IsFirstOrderThickening ι] (θ : Parameter G ι) :
    derivationOfParameter G ι θ =
      (d[sourceRestrict G ι]).postcomp
        ((SheafOfModules.forget (structureSheaf (arrowRestrict G ι)) ⋙
            PresheafOfModules.restrictScalars
              (𝟙 (structureSheaf (arrowRestrict G ι)).obj)).map
          ((Modules.pullbackPushforwardAdjunction
              (identityRestrict G ι)).homEquiv _ _ θ)) := rfl

/-- The commuting square of an infinitesimal section over the shared reduced map
`identityRestrict`. -/
theorem infinitesimalCommSq [IsFirstOrderThickening ι] (δ : InfinitesimalSection G ι) :
    CommSq (identityRestrict G ι) ι (arrowι G ι) δ.arrow.left :=
  ⟨δ.restrict⟩

/-- The inverse-image form of `e^♯`, as a map
`identityRestrict⁻¹(arrowι⁻¹ 𝒪_R) ⟶ ι⁻¹ 𝒪_U`. -/
def identityStructureMap [IsFirstOrderThickening ι] :
    inverseImageClosedStructureSheaf (identityRestrict G ι) (arrowι G ι) ⟶
      closedStructureSheaf ι :=
  structureMap_transported ι (arrowι G ι) (identityRestrict G ι) G.e.left
    (identityCommSq G ι).w.symm

/-- Unfolding of `identityStructureMap`. -/
theorem identityStructureMap_eq [IsFirstOrderThickening ι] :
    identityStructureMap G ι =
      structureMap_transported ι (arrowι G ι) (identityRestrict G ι) G.e.left
        (identityCommSq G ι).w.symm := rfl

/-- The inverse-image form of `δ^♯`, as a map
`identityRestrict⁻¹(arrowι⁻¹ 𝒪_R) ⟶ ι⁻¹ 𝒪_U` over the shared reduced square. -/
def infinitesimalStructureMap [IsFirstOrderThickening ι] (δ : InfinitesimalSection G ι) :
    inverseImageClosedStructureSheaf (identityRestrict G ι) (arrowι G ι) ⟶
      closedStructureSheaf ι :=
  structureMap_transported ι (arrowι G ι) (identityRestrict G ι) δ.arrow.left
    (infinitesimalCommSq G ι δ).w.symm

/-- Unfolding of `infinitesimalStructureMap`. -/
theorem infinitesimalStructureMap_eq [IsFirstOrderThickening ι]
    (δ : InfinitesimalSection G ι) :
    infinitesimalStructureMap G ι δ =
      structureMap_transported ι (arrowι G ι) (identityRestrict G ι) δ.arrow.left
        (infinitesimalCommSq G ι δ).w.symm := rfl

/-- Projection of `identityRestrict⁻¹(arrowι⁻¹ 𝒪_R)` onto `identityRestrict⁻¹ 𝒪_{R₀}`
along `arrowι^♯`. -/
def targetProjection [IsFirstOrderThickening ι] :
    inverseImageClosedStructureSheaf (identityRestrict G ι) (arrowι G ι) ⟶
      (spacesRingedToposHom (identityRestrict G ι)).toTopos.ringInverseImage.obj
        (spacesStructureSheaf (arrowRestrict G ι)) :=
  (spacesRingedToposHom (identityRestrict G ι)).toTopos.ringInverseImage.map
    (closedStructureSheaf_structureMap (arrowι G ι))

/-- Unfolding of `targetProjection`. -/
theorem targetProjection_eq [IsFirstOrderThickening ι] :
    targetProjection G ι =
      (spacesRingedToposHom (identityRestrict G ι)).toTopos.ringInverseImage.map
        (closedStructureSheaf_structureMap (arrowι G ι)) := rfl

/-- The value of the structure-sheaf difference of `δ` and `e` on a local section of
`identityRestrict⁻¹(arrowι⁻¹ 𝒪_R)`. -/
def structureMapDifference_apply [IsFirstOrderThickening ι] (δ : InfinitesimalSection G ι)
    (V : (spacesEtaleSite U₀)ᵒᵖ)
    (x : (inverseImageClosedStructureSheaf (identityRestrict G ι) (arrowι G ι)).obj.obj V) :
    (closedStructureSheaf ι).obj.obj V :=
  (infinitesimalStructureMap G ι δ).hom.app V x -
    (identityStructureMap G ι).hom.app V x

/-- Unfolding of `structureMapDifference_apply`. -/
theorem structureMapDifference_apply_eq [IsFirstOrderThickening ι]
    (δ : InfinitesimalSection G ι) (V : (spacesEtaleSite U₀)ᵒᵖ)
    (x : (inverseImageClosedStructureSheaf (identityRestrict G ι) (arrowι G ι)).obj.obj V) :
    structureMapDifference_apply G ι δ V x =
      (infinitesimalStructureMap G ι δ).hom.app V x -
        (identityStructureMap G ι).hom.app V x := rfl

/-- Forget commutative-ring-valued sheaves on the spaces-étale site to abelian groups. -/
abbrev forgetSpacesRing (X : AlgebraicSpace S) :
    Sheaf (spacesEtaleTopology X) RingCat.{u} ⥤
      Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u} :=
  sheafCompose (spacesEtaleTopology X) (forget₂ RingCat AddCommGrpCat.{u})

/-- The additive difference of the inverse-image structure maps of `δ` and `e`. -/
def structureMapDifference [IsFirstOrderThickening ι] (δ : InfinitesimalSection G ι) :
    (forgetSpacesRing U₀).obj
        (inverseImageClosedStructureSheaf (identityRestrict G ι) (arrowι G ι)) ⟶
      (forgetSpacesRing U₀).obj (closedStructureSheaf ι) :=
  (forgetSpacesRing U₀).map (infinitesimalStructureMap G ι δ) -
    (forgetSpacesRing U₀).map (identityStructureMap G ι)

/-- Unfolding of `structureMapDifference`. -/
theorem structureMapDifference_eq [IsFirstOrderThickening ι] (δ : InfinitesimalSection G ι) :
    structureMapDifference G ι δ =
      (forgetSpacesRing U₀).map (infinitesimalStructureMap G ι δ) -
        (forgetSpacesRing U₀).map (identityStructureMap G ι) := rfl

/-- Underlying additive values of `derivationOfParameter θ` on étale objects of `R₀`. -/
def derivationOfParameter_apply [IsFirstOrderThickening ι] (θ : Parameter G ι)
    (W : (smallEtaleSite (arrowRestrict G ι))ᵒᵖ)
    (a : (commStructureSheaf (arrowRestrict G ι)).obj.obj W) :
    (toCommPresheaf
        ((Modules.pushforward (identityRestrict G ι)).obj
          (thickeningConormal ι))).obj W :=
  (derivationOfParameter G ι θ).d a

/-- Unfolding of `derivationOfParameter_apply`. -/
theorem derivationOfParameter_apply_eq [IsFirstOrderThickening ι] (θ : Parameter G ι)
    (W : (smallEtaleSite (arrowRestrict G ι))ᵒᵖ)
    (a : (commStructureSheaf (arrowRestrict G ι)).obj.obj W) :
    derivationOfParameter_apply G ι θ W a =
      (derivationOfParameter G ι θ).d a := rfl

/-- The additive sheaf morphism on `U₀,étale` associated to a parameter `θ`. -/
def parameterToConormal [IsFirstOrderThickening ι] (θ : Parameter G ι) :
    (SheafOfModules.toSheaf (structureSheaf U₀)).obj
        ((Modules.pullback (identityRestrict G ι)).obj Ω[sourceRestrict G ι]) ⟶
      (SheafOfModules.toSheaf (structureSheaf U₀)).obj (thickeningConormal ι) :=
  (SheafOfModules.toSheaf (structureSheaf U₀)).map θ

/-- Unfolding of `parameterToConormal`. -/
theorem parameterToConormal_eq [IsFirstOrderThickening ι] (θ : Parameter G ι) :
    parameterToConormal G ι θ =
      (SheafOfModules.toSheaf (structureSheaf U₀)).map θ := rfl

/-- Restriction of abelian sheaves from `U₀_spaces,étale` to `U₀,étale`. -/
abbrev restrictSpacesAdd (X : AlgebraicSpace S) :
    Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u} ⥤
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u} :=
  (smallEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u}
    (smallEtaleTopology X) (spacesEtaleTopology X)

/-- The additive difference of `δ` and `e`, restricted to the small étale site of `U₀`. -/
def structureMapDifference_restrict [IsFirstOrderThickening ι]
    (δ : InfinitesimalSection G ι) :
    (restrictSpacesAdd U₀).obj
        ((forgetSpacesRing U₀).obj
          (inverseImageClosedStructureSheaf (identityRestrict G ι) (arrowι G ι))) ⟶
      (restrictSpacesAdd U₀).obj
        ((forgetSpacesRing U₀).obj (closedStructureSheaf ι)) :=
  (restrictSpacesAdd U₀).map (structureMapDifference G ι δ)

/-- Unfolding of `structureMapDifference_restrict`. -/
theorem structureMapDifference_restrict_eq [IsFirstOrderThickening ι]
    (δ : InfinitesimalSection G ι) :
    structureMapDifference_restrict G ι δ =
      (restrictSpacesAdd U₀).map (structureMapDifference G ι δ) := rfl

/-- Left Kan extensions of abelian-group presheaves along the opposite of étale base
change exist on the small étale sites of algebraic spaces. -/
instance etaleBaseChange_op_hasLeftKanExtension_addCommGrpCat
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (F : (smallEtaleSite Y)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (etaleBaseChange f).op.HasLeftKanExtension F :=
  sorry

/-- Abelian-group-valued weak sheafification exists on the étale site of algebraic
spaces. -/
instance spacesEtaleTopology_hasWeakSheafify_addCommGrpCat (X : AlgebraicSpace S) :
    HasWeakSheafify (spacesEtaleTopology X) AddCommGrpCat.{u} :=
  sorry

/-- The opposite of the small étale inclusion has pointwise right Kan extensions on
abelian-group presheaves. -/
instance smallEtaleInclusion_op_hasPointwiseRightKanExtension_addCommGrp
    (X : AlgebraicSpace S) (P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (smallEtaleInclusion X).op.HasPointwiseRightKanExtension P :=
  sorry

/-- The small étale inclusion is cocontinuous, so abelian sheaves extend from
`X_étale` to `X_spaces,étale`. -/
instance smallEtaleInclusion_isCocontinuous (X : AlgebraicSpace S) :
    (smallEtaleInclusion X).IsCocontinuous (smallEtaleTopology X)
      (spacesEtaleTopology X) :=
  sorry

/-- Inverse image of abelian sheaves along a morphism of algebraic spaces. -/
def addInverseImage {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u} ⥤
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u} :=
  Functor.sheafPullbackConstruction.sheafPullback (etaleBaseChange f) AddCommGrpCat.{u}
      (smallEtaleTopology Y) (spacesEtaleTopology X) ⋙
    (smallEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u}
      (smallEtaleTopology X) (spacesEtaleTopology X)

/-- `addInverseImage f` is sheaf pullback along `etaleBaseChange f` followed by restriction. -/
theorem addInverseImage_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    addInverseImage f =
      Functor.sheafPullbackConstruction.sheafPullback (etaleBaseChange f) AddCommGrpCat.{u}
          (smallEtaleTopology Y) (spacesEtaleTopology X) ⋙
        (smallEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u}
          (smallEtaleTopology X) (spacesEtaleTopology X) :=
  rfl

/-- Naturality of the additive maps underlying a relative derivation on algebraic spaces. -/
theorem derivationAdditiveMap_naturality {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (F : X.Modules) (D : AlgebraicSpace.Hom.derivations f F)
    {U V : (smallEtaleSite X)ᵒᵖ} (g : U ⟶ V) :
    ((sheafCompose (smallEtaleTopology X) (forget₂ RingCat AddCommGrpCat.{u})).obj
        ((sheafCompose (smallEtaleTopology X)
            (forget₂ CommRingCat RingCat.{u})).obj
          (commStructureSheaf X))).obj.map g ≫ AddCommGrpCat.ofHom D.d =
      AddCommGrpCat.ofHom D.d ≫
        ((SheafOfModules.toSheaf (structureSheaf X)).obj F).obj.map g :=
  sorry

/-- The underlying presheaf morphism of a relative derivation. -/
def derivationAdditiveMap_presheaf {X Y : AlgebraicSpace S} (f : X ⟶ Y) (F : X.Modules)
    (D : AlgebraicSpace.Hom.derivations f F) :
    ((sheafCompose (smallEtaleTopology X) (forget₂ RingCat AddCommGrpCat.{u})).obj
        ((sheafCompose (smallEtaleTopology X)
            (forget₂ CommRingCat RingCat.{u})).obj
          (commStructureSheaf X))).obj ⟶
      ((SheafOfModules.toSheaf (structureSheaf X)).obj F).obj :=
  { app := fun _ ↦ AddCommGrpCat.ofHom D.d
    naturality := fun _ _ g ↦ derivationAdditiveMap_naturality f F D g }

/-- The additive sheaf morphism underlying a relative derivation. -/
def derivationAdditiveMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) (F : X.Modules)
    (D : AlgebraicSpace.Hom.derivations f F) :
    (sheafCompose (smallEtaleTopology X) (forget₂ RingCat AddCommGrpCat.{u})).obj
        ((sheafCompose (smallEtaleTopology X)
            (forget₂ CommRingCat RingCat.{u})).obj
          (commStructureSheaf X)) ⟶
      (SheafOfModules.toSheaf (structureSheaf X)).obj F :=
  InducedCategory.homMk (derivationAdditiveMap_presheaf f F D)

/-- Unfolding of `derivationAdditiveMap`. -/
theorem derivationAdditiveMap_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) (F : X.Modules)
    (D : AlgebraicSpace.Hom.derivations f F) :
    derivationAdditiveMap f F D =
      InducedCategory.homMk (derivationAdditiveMap_presheaf f F D) :=
  rfl

/-- On a first-order thickening, the projection `I ⟶ I/I²` is an isomorphism. -/
instance instIsIso_quotientByIdeal_π {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsFirstOrderThickening i] :
    IsIso (Modules.quotientByIdeal.π (AlgebraicSpace.Hom.idealSheafSubobject i)
      (AlgebraicSpace.Hom.idealSheaf i)) :=
  sorry

/-- The coborder lift of a first-order thickening remains a first-order thickening. -/
instance instIsFirstOrderThickening_liftCoborder {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsFirstOrderThickening i] :
    IsFirstOrderThickening (AlgebraicSpace.IsImmersion.liftCoborder i) :=
  sorry

/-- The module inclusion `I/I² ⟶ 𝒪` of a first-order thickening. -/
def firstOrderIdealIncl {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsFirstOrderThickening i] :
    Modules.quotientByIdeal (AlgebraicSpace.Hom.idealSheafSubobject i)
        (AlgebraicSpace.Hom.idealSheaf i) ⟶
      SheafOfModules.unit (structureSheaf X) :=
  inv (Modules.quotientByIdeal.π (AlgebraicSpace.Hom.idealSheafSubobject i)
      (AlgebraicSpace.Hom.idealSheaf i)) ≫
    AlgebraicSpace.Hom.idealSheafι i

/-- Unfolding of `firstOrderIdealIncl`. -/
theorem firstOrderIdealIncl_eq {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsFirstOrderThickening i] :
    firstOrderIdealIncl i =
      inv (Modules.quotientByIdeal.π (AlgebraicSpace.Hom.idealSheafSubobject i)
          (AlgebraicSpace.Hom.idealSheaf i)) ≫
        AlgebraicSpace.Hom.idealSheafι i :=
  rfl

/-- The additive inclusion of `I/I²` into the structure sheaf of a first-order thickening. -/
def firstOrderIdealInclAdd {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsFirstOrderThickening i] :
    (SheafOfModules.toSheaf (structureSheaf X)).obj
        (Modules.quotientByIdeal (AlgebraicSpace.Hom.idealSheafSubobject i)
          (AlgebraicSpace.Hom.idealSheaf i)) ⟶
      (SheafOfModules.toSheaf (structureSheaf X)).obj
        (SheafOfModules.unit (structureSheaf X)) :=
  (SheafOfModules.toSheaf (structureSheaf X)).map (firstOrderIdealIncl i)

/-- Unfolding of `firstOrderIdealInclAdd`. -/
theorem firstOrderIdealInclAdd_eq {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsFirstOrderThickening i] :
    firstOrderIdealInclAdd i =
      (SheafOfModules.toSheaf (structureSheaf X)).map (firstOrderIdealIncl i) :=
  rfl

/-- Inverse image of the universal `s₀`-derivation along `e₀`. -/
def pulledUniversalDerivation [IsFirstOrderThickening ι] :
    (addInverseImage (identityRestrict G ι)).obj
        ((sheafCompose (smallEtaleTopology (arrowRestrict G ι))
            (forget₂ RingCat AddCommGrpCat.{u})).obj
          ((sheafCompose (smallEtaleTopology (arrowRestrict G ι))
              (forget₂ CommRingCat RingCat.{u})).obj
            (commStructureSheaf (arrowRestrict G ι)))) ⟶
      (addInverseImage (identityRestrict G ι)).obj
        ((SheafOfModules.toSheaf (structureSheaf (arrowRestrict G ι))).obj
          Ω[sourceRestrict G ι]) :=
  (addInverseImage (identityRestrict G ι)).map
    (derivationAdditiveMap (sourceRestrict G ι)
      (Ω[sourceRestrict G ι]) (d[sourceRestrict G ι]))

/-- Unfolding of `pulledUniversalDerivation`. -/
theorem pulledUniversalDerivation_eq [IsFirstOrderThickening ι] :
    pulledUniversalDerivation G ι =
      (addInverseImage (identityRestrict G ι)).map
        (derivationAdditiveMap (sourceRestrict G ι)
          (Ω[sourceRestrict G ι]) (d[sourceRestrict G ι])) :=
  rfl

/-- Inverse image of the adjunction unit `Ω[s₀] ⟶ e₀_* e₀^* Ω[s₀]`. -/
def pulledDifferentialsUnit [IsFirstOrderThickening ι] :
    (addInverseImage (identityRestrict G ι)).obj
        ((SheafOfModules.toSheaf (structureSheaf (arrowRestrict G ι))).obj
          Ω[sourceRestrict G ι]) ⟶
      (addInverseImage (identityRestrict G ι)).obj
        ((SheafOfModules.toSheaf (structureSheaf (arrowRestrict G ι))).obj
          ((Modules.pushforward (identityRestrict G ι)).obj
            ((Modules.pullback (identityRestrict G ι)).obj
              Ω[sourceRestrict G ι]))) :=
  (addInverseImage (identityRestrict G ι)).map
    ((SheafOfModules.toSheaf (structureSheaf (arrowRestrict G ι))).map
      ((Modules.pullbackPushforwardAdjunction (identityRestrict G ι)).unit.app
        Ω[sourceRestrict G ι]))

/-- Unfolding of `pulledDifferentialsUnit`. -/
theorem pulledDifferentialsUnit_eq [IsFirstOrderThickening ι] :
    pulledDifferentialsUnit G ι =
      (addInverseImage (identityRestrict G ι)).map
        ((SheafOfModules.toSheaf (structureSheaf (arrowRestrict G ι))).map
          ((Modules.pullbackPushforwardAdjunction (identityRestrict G ι)).unit.app
            Ω[sourceRestrict G ι])) :=
  rfl

/-- Inverse image of the additive inclusion `I/I² ⟶ 𝒪_U` along the coborder lift. -/
def pulledFirstOrderIdealIncl [IsFirstOrderThickening ι] :
    (addInverseImage (AlgebraicSpace.IsImmersion.liftCoborder ι)).obj
        ((SheafOfModules.toSheaf
            (structureSheaf ((AlgebraicSpace.IsImmersion.coborderRange ι).X))).obj
          (Modules.quotientByIdeal
            (AlgebraicSpace.Hom.idealSheafSubobject
              (AlgebraicSpace.IsImmersion.liftCoborder ι))
            (AlgebraicSpace.Hom.idealSheaf
              (AlgebraicSpace.IsImmersion.liftCoborder ι)))) ⟶
      (addInverseImage (AlgebraicSpace.IsImmersion.liftCoborder ι)).obj
        ((SheafOfModules.toSheaf
            (structureSheaf ((AlgebraicSpace.IsImmersion.coborderRange ι).X))).obj
          (SheafOfModules.unit
            (structureSheaf ((AlgebraicSpace.IsImmersion.coborderRange ι).X)))) :=
  (addInverseImage (AlgebraicSpace.IsImmersion.liftCoborder ι)).map
    (firstOrderIdealInclAdd (AlgebraicSpace.IsImmersion.liftCoborder ι))

/-- Unfolding of `pulledFirstOrderIdealIncl`. -/
theorem pulledFirstOrderIdealIncl_eq [IsFirstOrderThickening ι] :
    pulledFirstOrderIdealIncl G ι =
      (addInverseImage (AlgebraicSpace.IsImmersion.liftCoborder ι)).map
        (firstOrderIdealInclAdd (AlgebraicSpace.IsImmersion.liftCoborder ι)) :=
  rfl

/-- The two presentations of `e₀⁻¹ 𝒪_{R₀}` on `U₀,étale` agree. -/
theorem restrictedTarget_eq_pulledStructure [IsFirstOrderThickening ι] :
    (restrictSpacesAdd U₀).obj
        ((forgetSpacesRing U₀).obj
          ((spacesRingedToposHom (identityRestrict G ι)).toTopos.ringInverseImage.obj
            (spacesStructureSheaf (arrowRestrict G ι)))) =
      (addInverseImage (identityRestrict G ι)).obj
        ((sheafCompose (smallEtaleTopology (arrowRestrict G ι))
            (forget₂ RingCat AddCommGrpCat.{u})).obj
          ((sheafCompose (smallEtaleTopology (arrowRestrict G ι))
              (forget₂ CommRingCat RingCat.{u})).obj
            (commStructureSheaf (arrowRestrict G ι)))) :=
  sorry

/-- Inverse image of the derivation associated to a parameter. -/
def pulledDerivationOfParameter [IsFirstOrderThickening ι] (θ : Parameter G ι) :
    (addInverseImage (identityRestrict G ι)).obj
        ((sheafCompose (smallEtaleTopology (arrowRestrict G ι))
            (forget₂ RingCat AddCommGrpCat.{u})).obj
          ((sheafCompose (smallEtaleTopology (arrowRestrict G ι))
              (forget₂ CommRingCat RingCat.{u})).obj
            (commStructureSheaf (arrowRestrict G ι)))) ⟶
      (addInverseImage (identityRestrict G ι)).obj
        ((SheafOfModules.toSheaf (structureSheaf (arrowRestrict G ι))).obj
          ((Modules.pushforward (identityRestrict G ι)).obj (thickeningConormal ι))) :=
  (addInverseImage (identityRestrict G ι)).map
    (derivationAdditiveMap (sourceRestrict G ι)
      ((Modules.pushforward (identityRestrict G ι)).obj (thickeningConormal ι))
      (derivationOfParameter G ι θ))

/-- Unfolding of `pulledDerivationOfParameter`. -/
theorem pulledDerivationOfParameter_eq [IsFirstOrderThickening ι] (θ : Parameter G ι) :
    pulledDerivationOfParameter G ι θ =
      (addInverseImage (identityRestrict G ι)).map
        (derivationAdditiveMap (sourceRestrict G ι)
          ((Modules.pushforward (identityRestrict G ι)).obj (thickeningConormal ι))
          (derivationOfParameter G ι θ)) :=
  rfl

/-- Geometric inverse image of `e₀_* 𝒞` agrees with the underlying sheaf of `e₀^* e₀_* 𝒞`. -/
theorem pulledPushforward_eq_modulePullback [IsFirstOrderThickening ι] :
    (addInverseImage (identityRestrict G ι)).obj
        ((SheafOfModules.toSheaf (structureSheaf (arrowRestrict G ι))).obj
          ((Modules.pushforward (identityRestrict G ι)).obj (thickeningConormal ι))) =
      (SheafOfModules.toSheaf (structureSheaf U₀)).obj
        ((Modules.pullback (identityRestrict G ι)).obj
          ((Modules.pushforward (identityRestrict G ι)).obj (thickeningConormal ι))) :=
  sorry

/-- The counit `e₀⁻¹ e₀_* 𝒞 ⟶ 𝒞` on underlying additive sheaves. -/
def pulledConormalCounit [IsFirstOrderThickening ι] :
    (addInverseImage (identityRestrict G ι)).obj
        ((SheafOfModules.toSheaf (structureSheaf (arrowRestrict G ι))).obj
          ((Modules.pushforward (identityRestrict G ι)).obj (thickeningConormal ι))) ⟶
      (SheafOfModules.toSheaf (structureSheaf U₀)).obj (thickeningConormal ι) :=
  eqToHom (pulledPushforward_eq_modulePullback G ι) ≫
    (SheafOfModules.toSheaf (structureSheaf U₀)).map
      ((Modules.pullbackPushforwardAdjunction (identityRestrict G ι)).counit.app
        (thickeningConormal ι))

/-- Unfolding of `pulledConormalCounit`. -/
theorem pulledConormalCounit_eq [IsFirstOrderThickening ι] :
    pulledConormalCounit G ι =
      eqToHom (pulledPushforward_eq_modulePullback G ι) ≫
        (SheafOfModules.toSheaf (structureSheaf U₀)).map
          ((Modules.pullbackPushforwardAdjunction (identityRestrict G ι)).counit.app
            (thickeningConormal ι)) :=
  rfl

/-- The two presentations of `𝒞_{U₀/U}` as an inverse image of `I/I²` agree. -/
theorem conormal_eq_pulledIdeal [IsFirstOrderThickening ι] :
    (SheafOfModules.toSheaf (structureSheaf U₀)).obj (thickeningConormal ι) =
      (addInverseImage (AlgebraicSpace.IsImmersion.liftCoborder ι)).obj
        ((SheafOfModules.toSheaf
            (structureSheaf (AlgebraicSpace.IsImmersion.coborderRange ι).X)).obj
          (Modules.quotientByIdeal
            (AlgebraicSpace.Hom.idealSheafSubobject
              (AlgebraicSpace.IsImmersion.liftCoborder ι))
            (AlgebraicSpace.Hom.idealSheaf
              (AlgebraicSpace.IsImmersion.liftCoborder ι)))) :=
  sorry

/-- The two presentations of `ι⁻¹ 𝒪_U` on `U₀,étale` agree. -/
theorem pulledAmbient_eq_closedStructure [IsFirstOrderThickening ι] :
    (addInverseImage (AlgebraicSpace.IsImmersion.liftCoborder ι)).obj
        ((SheafOfModules.toSheaf
            (structureSheaf (AlgebraicSpace.IsImmersion.coborderRange ι).X)).obj
          (SheafOfModules.unit
            (structureSheaf (AlgebraicSpace.IsImmersion.coborderRange ι).X))) =
      (restrictSpacesAdd U₀).obj
        ((forgetSpacesRing U₀).obj (closedStructureSheaf ι)) :=
  sorry

/-- Comparison from the restricted inverse-image presentation of `𝒪_R` to `e₀^* Ω[s₀]`. -/
def parameterProj [IsFirstOrderThickening ι] :
    (restrictSpacesAdd U₀).obj
        ((forgetSpacesRing U₀).obj
          (inverseImageClosedStructureSheaf (identityRestrict G ι) (arrowι G ι))) ⟶
      (addInverseImage (identityRestrict G ι)).obj
        ((sheafCompose (smallEtaleTopology (arrowRestrict G ι))
            (forget₂ RingCat AddCommGrpCat.{u})).obj
          ((sheafCompose (smallEtaleTopology (arrowRestrict G ι))
              (forget₂ CommRingCat RingCat.{u})).obj
            (commStructureSheaf (arrowRestrict G ι)))) :=
  (restrictSpacesAdd U₀).map ((forgetSpacesRing U₀).map (targetProjection G ι)) ≫
    eqToHom (restrictedTarget_eq_pulledStructure G ι)

/-- Comparison from `e₀_* 𝒞_{U₀/U}` to the restriction of `ι⁻¹ 𝒪_U`. -/
def parameterIncl [IsFirstOrderThickening ι] :
    (addInverseImage (identityRestrict G ι)).obj
        ((SheafOfModules.toSheaf (structureSheaf (arrowRestrict G ι))).obj
          ((Modules.pushforward (identityRestrict G ι)).obj (thickeningConormal ι))) ⟶
      (restrictSpacesAdd U₀).obj
        ((forgetSpacesRing U₀).obj (closedStructureSheaf ι)) :=
  pulledConormalCounit G ι ≫
    eqToHom (conormal_eq_pulledIdeal G ι) ≫
      pulledFirstOrderIdealIncl G ι ≫
        eqToHom (pulledAmbient_eq_closedStructure G ι)

/-- The additive map induced by `θ`, as a morphism of small étale abelian sheaves on `U₀`. -/
def parameterSheafMap [IsFirstOrderThickening ι] (θ : Parameter G ι) :
    (restrictSpacesAdd U₀).obj
        ((forgetSpacesRing U₀).obj
          (inverseImageClosedStructureSheaf (identityRestrict G ι) (arrowι G ι))) ⟶
      (restrictSpacesAdd U₀).obj
        ((forgetSpacesRing U₀).obj (closedStructureSheaf ι)) :=
  parameterProj G ι ≫ pulledDerivationOfParameter G ι θ ≫ parameterIncl G ι

/-- Unfolding of `parameterSheafMap`. -/
theorem parameterSheafMap_eq [IsFirstOrderThickening ι] (θ : Parameter G ι) :
    parameterSheafMap G ι θ =
      parameterProj G ι ≫ pulledDerivationOfParameter G ι θ ≫ parameterIncl G ι :=
  rfl

/-- `δ` is the first-order perturbation of the identity section by `θ`.

This is the source relation `δ = θ · e`: the additive difference of the
inverse-image structure maps of `δ` and `e` equals the image of
`derivationOfParameter G ι θ`. -/
def IsPerturbation [IsFirstOrderThickening ι] (θ : Parameter G ι)
    (δ : InfinitesimalSection G ι) : Prop :=
  structureMapDifference_restrict G ι δ = parameterSheafMap G ι θ

/-- Unfolding of `IsPerturbation`. -/
theorem isPerturbation_iff [IsFirstOrderThickening ι] (θ : Parameter G ι)
    (δ : InfinitesimalSection G ι) :
    IsPerturbation G ι θ δ ↔
      structureMapDifference_restrict G ι δ = parameterSheafMap G ι θ := sorry

/-- The identity structure map, forgotten to abelian sheaves on `U₀_spaces,étale`. -/
def identityStructureMapAdd [IsFirstOrderThickening ι] :
    (forgetSpacesRing U₀).obj
        (inverseImageClosedStructureSheaf (identityRestrict G ι) (arrowι G ι)) ⟶
      (forgetSpacesRing U₀).obj (closedStructureSheaf ι) :=
  (forgetSpacesRing U₀).map (identityStructureMap G ι)

/-- Unfolding of `identityStructureMapAdd`. -/
theorem identityStructureMapAdd_eq [IsFirstOrderThickening ι] :
    identityStructureMapAdd G ι =
      (forgetSpacesRing U₀).map (identityStructureMap G ι) :=
  rfl

/-- The small étale additive comparison `e^♯ + D_θ`. -/
def perturbIdentitySheafMap [IsFirstOrderThickening ι] (θ : Parameter G ι) :
    (restrictSpacesAdd U₀).obj
        ((forgetSpacesRing U₀).obj
          (inverseImageClosedStructureSheaf (identityRestrict G ι) (arrowι G ι))) ⟶
      (restrictSpacesAdd U₀).obj
        ((forgetSpacesRing U₀).obj (closedStructureSheaf ι)) :=
  (restrictSpacesAdd U₀).map (identityStructureMapAdd G ι) + parameterSheafMap G ι θ

/-- Unfolding of `perturbIdentitySheafMap`. -/
theorem perturbIdentitySheafMap_eq [IsFirstOrderThickening ι] (θ : Parameter G ι) :
    perturbIdentitySheafMap G ι θ =
      (restrictSpacesAdd U₀).map (identityStructureMapAdd G ι) +
        parameterSheafMap G ι θ :=
  rfl

/-- Sectionwise formula for the perturbed structure map: `e^♯ + D_θ`. This is the
spaces analogue of `Scheme.Hom.Deformation.presentationPerturbApply`. -/
def perturbIdentityApply [IsFirstOrderThickening ι] (θ : Parameter G ι)
    (V : (smallEtaleSite U₀)ᵒᵖ)
    (x : ((restrictSpacesAdd U₀).obj
        ((forgetSpacesRing U₀).obj
          (inverseImageClosedStructureSheaf (identityRestrict G ι)
            (arrowι G ι)))).obj.obj V) :
    ((restrictSpacesAdd U₀).obj
        ((forgetSpacesRing U₀).obj (closedStructureSheaf ι))).obj.obj V :=
  (perturbIdentitySheafMap G ι θ).hom.app V x

/-- Unfolding of `perturbIdentityApply`. -/
theorem perturbIdentityApply_eq [IsFirstOrderThickening ι] (θ : Parameter G ι)
    (V : (smallEtaleSite U₀)ᵒᵖ)
    (x : ((restrictSpacesAdd U₀).obj
        ((forgetSpacesRing U₀).obj
          (inverseImageClosedStructureSheaf (identityRestrict G ι)
            (arrowι G ι)))).obj.obj V) :
    perturbIdentityApply G ι θ V x =
      (perturbIdentitySheafMap G ι θ).hom.app V x :=
  rfl

/-- The sectionwise perturbation preserves zero. -/
theorem perturbIdentityApply_zero [IsFirstOrderThickening ι] (θ : Parameter G ι)
    (V : (smallEtaleSite U₀)ᵒᵖ) :
    perturbIdentityApply G ι θ V 0 = 0 :=
  sorry

/-- The sectionwise perturbation preserves addition. -/
theorem perturbIdentityApply_add [IsFirstOrderThickening ι] (θ : Parameter G ι)
    (V : (smallEtaleSite U₀)ᵒᵖ)
    (x y : ((restrictSpacesAdd U₀).obj
        ((forgetSpacesRing U₀).obj
          (inverseImageClosedStructureSheaf (identityRestrict G ι)
            (arrowι G ι)))).obj.obj V) :
    perturbIdentityApply G ι θ V (x + y) =
      perturbIdentityApply G ι θ V x + perturbIdentityApply G ι θ V y :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
