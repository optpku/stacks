module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import ReasLib.CategoryTheory.Sites.Topos.TwoMorphism
public import stacks_project.Chap07.Definition_7_14_1
public import stacks_project.Chap85.Lemma_85_3_4_Comparison
public import stacks_project.Chap85.Lemma_85_3_5_Stage
public import stacks_project.Chap85.Remark_85_4_1_MorphismDiagram

/-!
# Augmentation morphisms of topoi, covariant case

An exact-site augmentation `u0` of a morphism diagram induces stage morphisms of
topoi `a_n` and a total morphism `a : Sh(C_total) ⟶ Sh(D)` whose inverse image is
the sheaf system of the functors `a_n⁻¹` and whose direct image is the equalizer of
the two coface maps `a_{0,*} F_0 ⇉ a_{1,*} F_1`.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MorphismOfTopoiIn Simplicial

noncomputable section

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : D ⥤ C.obj ⦋0⦌)
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ P : Dᵒᵖ ⥤ Type w, u0.op.HasLeftKanExtension P]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck (Type w))]
variable [h_morphism : IsMorphismDiagram C J]
variable [h_aug : IsAugmentation C J K u0]
include h_morphism
include h_aug

/-- Structure-map morphism of topoi `f_φ` of the ambient morphism diagram. -/
abbrev IsAugmentation.faceTopos {m n : SimplexCategory} (φ : m ⟶ n) :
    MorphismOfTopoiIn (J m).toGrothendieck (J n).toGrothendieck :=
  SimplicialSites.toposMap.{u, v, w} C J φ


/-- The common composite `u_n = u_φ ∘ u0` is an exact morphism of sites
`(D, K) ⟶ (C.obj n, J n)`. -/
instance IsAugmentation.stageFunctor_isExactMorphism (n : SimplexCategory) :
    IsExactMorphismOfSites K.toGrothendieck (J n).toGrothendieck
      (IsAugmentation.stageFunctor C u0 n) :=
  sorry

/-- Sheaf pullback along the stage functor `u_n` preserves finite limits. -/
instance IsAugmentation.stageFunctor_preservesFiniteLimits_sheafPullback
    (n : SimplexCategory) :
    PreservesFiniteLimits
      ((IsAugmentation.stageFunctor C u0 n).sheafPullback (Type w)
        K.toGrothendieck (J n).toGrothendieck) :=
  sorry

/-- Identification `u_m ⋙ u_φ ≅ u_n` of presenting functors along a simplex operator. -/
def IsAugmentation.stageFunctor_compIso {m n : SimplexCategory} (φ : m ⟶ n) :
    IsAugmentation.stageFunctor C u0 m ⋙ (C.map φ).toFunctor ≅
      IsAugmentation.stageFunctor C u0 n :=
  Functor.associator u0 ((C.map (SimplexCategory.const ⦋0⦌ m 0)).toFunctor)
      (C.map φ).toFunctor ≪≫
    NatIso.hcomp (Iso.refl u0)
      (map_comp_toFunctor C (SimplexCategory.const ⦋0⦌ m 0) φ) ≪≫
    eqToIso (h_aug.map_eq (SimplexCategory.const ⦋0⦌ m 0 ≫ φ)
      (SimplexCategory.const ⦋0⦌ n 0))

/-- The morphism of topoi `a_n : Sh(C.obj n) ⟶ Sh(D)` presented by the common
composite `u_n`. -/
def IsAugmentation.stageTopos (n : SimplexCategory) :
    MorphismOfTopoiIn K.toGrothendieck (J n).toGrothendieck :=
  (IsAugmentation.stageFunctor C u0 n).morphismOfTopoiInOfContinuous
    K.toGrothendieck (J n).toGrothendieck

/-- Inverse image of `a_n` is sheaf pullback along `u_n`. -/
theorem IsAugmentation.stageTopos_inverseImage (n : SimplexCategory) :
    (IsAugmentation.stageTopos C J K u0 n)⁻¹ =
      (IsAugmentation.stageFunctor C u0 n).sheafPullback (Type w)
        K.toGrothendieck (J n).toGrothendieck :=
  sorry

/-- Direct image of `a_n` is continuous sheaf pushforward along `u_n`. -/
theorem IsAugmentation.stageTopos_pushforward (n : SimplexCategory) :
    (IsAugmentation.stageTopos C J K u0 n).pushforward =
      (IsAugmentation.stageFunctor C u0 n).sheafPushforwardContinuous (Type w)
        K.toGrothendieck (J n).toGrothendieck :=
  sorry

/-- Inverse-image form of `a_m ∘ f_φ = a_n`. -/
def IsAugmentation.stageTopos_comp {m n : SimplexCategory} (φ : m ⟶ n) :
    (IsAugmentation.stageTopos C J K u0 m)⁻¹ ⋙ (IsAugmentation.faceTopos C J φ)⁻¹ ≅
      (IsAugmentation.stageTopos C J K u0 n)⁻¹ :=
  Adjunction.leftAdjointUniq
    ((Adjunction.comp
        ((IsAugmentation.stageFunctor C u0 m).sheafAdjunctionContinuous (Type w)
          K.toGrothendieck (J m).toGrothendieck)
        ((C.map φ).toFunctor.sheafAdjunctionContinuous (Type w)
          (J m).toGrothendieck (J n).toGrothendieck)).ofNatIsoRight
      (Functor.sheafPushforwardContinuousComp'
        (IsAugmentation.stageFunctor_compIso C J K u0 φ) (Type w)
        K.toGrothendieck (J m).toGrothendieck (J n).toGrothendieck))
    ((IsAugmentation.stageFunctor C u0 n).sheafAdjunctionContinuous (Type w)
      K.toGrothendieck (J n).toGrothendieck)

/-- Direct-image mate of `a_m ∘ f_φ = a_n`. -/
def IsAugmentation.stageTopos_pushforward_comp {m n : SimplexCategory} (φ : m ⟶ n) :
    (IsAugmentation.faceTopos C J φ).pushforward ⋙ (IsAugmentation.stageTopos C J K u0 m).pushforward ≅
      (IsAugmentation.stageTopos C J K u0 n).pushforward :=
  MorphismOfTopoiIn.pushforwardIsoOfInverseImageIso
    (MorphismOfTopoiIn.comp (IsAugmentation.stageTopos C J K u0 m) (IsAugmentation.faceTopos C J φ))
    (IsAugmentation.stageTopos C J K u0 n)
    (IsAugmentation.stageTopos_comp C J K u0 φ)

/-- Pushforward-form transition of the inverse-image sheaf system at a simplex operator. -/
def IsAugmentation.inverseImageSystemMap (G : Sheaf K.toGrothendieck (Type w))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (IsAugmentation.stageTopos C J K u0 m)⁻¹.obj G ⟶
      (IsAugmentation.faceTopos C J φ).pushforward.obj
        ((IsAugmentation.stageTopos C J K u0 n)⁻¹.obj G) :=
  ((IsAugmentation.faceTopos C J φ).adjunction.homEquiv
      ((IsAugmentation.stageTopos C J K u0 m)⁻¹.obj G)
      ((IsAugmentation.stageTopos C J K u0 n)⁻¹.obj G))
    ((IsAugmentation.stageTopos_comp C J K u0 φ).hom.app G)

/-- The sheaf system whose stage sheaves are `a_n⁻¹ G` and whose transitions are the
identifications `f_φ⁻¹ a_m⁻¹ G ≅ a_n⁻¹ G`. -/
def IsAugmentation.inverseImageSystem :
    Sheaf K.toGrothendieck (Type w) ⥤
      SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ IsAugmentation.faceTopos C J φ) where
  obj G :=
    SheafSystem.of (fun n ↦ (IsAugmentation.stageTopos C J K u0 n)⁻¹.obj G)
      (fun {m n} φ ↦ IsAugmentation.inverseImageSystemMap C J K u0 G φ) sorry sorry
  map {G H} α :=
    SheafSystem.homMk (fun n ↦ (IsAugmentation.stageTopos C J K u0 n)⁻¹.map α) sorry
  map_id := sorry
  map_comp := sorry

/-- The stage sheaf of `inverseImageSystem.obj G` at `n` is `a_n⁻¹ G`. -/
theorem IsAugmentation.inverseImageSystem_obj (G : Sheaf K.toGrothendieck (Type w))
    (n : SimplexCategory) :
    ((IsAugmentation.inverseImageSystem C J K u0).obj G).obj n =
      (IsAugmentation.stageTopos C J K u0 n)⁻¹.obj G :=
  sorry

/-- Inverse image `a⁻¹` of the total augmentation morphism, sending `G` to the sheaf
on `C_total` assembled from the system of the sheaves `a_n⁻¹ G`. -/
def IsAugmentation.inverseImage :
    Sheaf K.toGrothendieck (Type w) ⥤ Sheaf (topology C J) (Type w) :=
  IsAugmentation.inverseImageSystem C J K u0 ⋙ ofSheafSystem C J

/-- Inverse image of a sheaf `G` is `ofSheafSystem` of the system of the sheaves `a_n⁻¹ G`. -/
theorem IsAugmentation.inverseImage_obj (G : Sheaf K.toGrothendieck (Type w)) :
    (IsAugmentation.inverseImage C J K u0).obj G =
      (ofSheafSystem C J).obj ((IsAugmentation.inverseImageSystem C J K u0).obj G) :=
  sorry

/-- Inverse image `a⁻¹` preserves finite limits. -/
instance IsAugmentation.inverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (IsAugmentation.inverseImage C J K u0) :=
  sorry

/-- The two maps `a_{0,*} F_0 ⇉ a_{1,*} F_1` induced by the coface operators `δ i`. -/
def IsAugmentation.pushforwardParallel (F : Sheaf (topology C J) (Type w)) (i : Fin 2) :
    (IsAugmentation.stageTopos C J K u0 ⦋0⦌).pushforward.obj
      (((toSheafSystem C J).obj F).obj ⦋0⦌) ⟶
      (IsAugmentation.stageTopos C J K u0 ⦋1⦌).pushforward.obj
        (((toSheafSystem C J).obj F).obj ⦋1⦌) :=
  (IsAugmentation.stageTopos C J K u0 ⦋0⦌).pushforward.map
      ((IsAugmentation.faceTopos C J (SimplexCategory.δ i : ⦋0⦌ ⟶ ⦋1⦌)).adjunction.unit.app
        (((toSheafSystem C J).obj F).obj ⦋0⦌)) ≫
    (IsAugmentation.stageTopos C J K u0 ⦋0⦌).pushforward.map
      ((IsAugmentation.faceTopos C J (SimplexCategory.δ i : ⦋0⦌ ⟶ ⦋1⦌)).pushforward.map
        (SheafSystem.mapInverseImage ((toSheafSystem C J).obj F)
          (SimplexCategory.δ i : ⦋0⦌ ⟶ ⦋1⦌))) ≫
    (IsAugmentation.stageTopos_pushforward_comp C J K u0
        (SimplexCategory.δ i : ⦋0⦌ ⟶ ⦋1⦌)).hom.app
      (((toSheafSystem C J).obj F).obj ⦋1⦌)

/-- Direct image `a_*`, sending a sheaf on `C_total` to the equalizer of
`a_{0,*} F_0 ⇉ a_{1,*} F_1`. -/
def IsAugmentation.pushforward :
    Sheaf (topology C J) (Type w) ⥤ Sheaf K.toGrothendieck (Type w) where
  obj F :=
    equalizer (IsAugmentation.pushforwardParallel C J K u0 F 0)
      (IsAugmentation.pushforwardParallel C J K u0 F 1)
  map {F G} α :=
    equalizer.lift
      (equalizer.ι (IsAugmentation.pushforwardParallel C J K u0 F 0)
          (IsAugmentation.pushforwardParallel C J K u0 F 1) ≫
        (IsAugmentation.stageTopos C J K u0 ⦋0⦌).pushforward.map
          (((toSheafSystem C J).map α).app ⦋0⦌))
      sorry
  map_id := sorry
  map_comp := sorry

/-- The object `a_* F` is the equalizer of the two coface maps. -/
theorem IsAugmentation.pushforward_obj (F : Sheaf (topology C J) (Type w)) :
    (IsAugmentation.pushforward C J K u0).obj F =
      equalizer (IsAugmentation.pushforwardParallel C J K u0 F 0)
        (IsAugmentation.pushforwardParallel C J K u0 F 1) :=
  sorry

/-- The comparison `a_* F ⟶ a_{0,*} F_0`. -/
def IsAugmentation.pushforwardι (F : Sheaf (topology C J) (Type w)) :
    (IsAugmentation.pushforward C J K u0).obj F ⟶
      (IsAugmentation.stageTopos C J K u0 ⦋0⦌).pushforward.obj
        (((toSheafSystem C J).obj F).obj ⦋0⦌) :=
  equalizer.ι (IsAugmentation.pushforwardParallel C J K u0 F 0)
    (IsAugmentation.pushforwardParallel C J K u0 F 1)

/-- The fork presenting `a_* F` as equalizer of `a_{0,*} F_0 ⇉ a_{1,*} F_1`. -/
def IsAugmentation.pushforwardFork (F : Sheaf (topology C J) (Type w)) :
    Fork (IsAugmentation.pushforwardParallel C J K u0 F 0)
      (IsAugmentation.pushforwardParallel C J K u0 F 1) :=
  equalizer.fork (IsAugmentation.pushforwardParallel C J K u0 F 0)
    (IsAugmentation.pushforwardParallel C J K u0 F 1)

/-- The two coface maps coequalize `pushforwardι`. -/
theorem IsAugmentation.pushforwardFork_condition (F : Sheaf (topology C J) (Type w)) :
    IsAugmentation.pushforwardι C J K u0 F ≫
        IsAugmentation.pushforwardParallel C J K u0 F 0 =
      IsAugmentation.pushforwardι C J K u0 F ≫
        IsAugmentation.pushforwardParallel C J K u0 F 1 :=
  sorry

/-- The mediating morphism into `a_* F` from a test cone. -/
def IsAugmentation.pushforwardForkLift (F : Sheaf (topology C J) (Type w))
    (s : Fork (IsAugmentation.pushforwardParallel C J K u0 F 0)
      (IsAugmentation.pushforwardParallel C J K u0 F 1)) :
    s.pt ⟶ (IsAugmentation.pushforward C J K u0).obj F :=
  equalizer.lift (Fork.ι s) sorry

/-- `a_* F` is the equalizer of the two maps `a_{0,*} F_0 ⇉ a_{1,*} F_1`. -/
def IsAugmentation.pushforwardFork_isLimit (F : Sheaf (topology C J) (Type w)) :
    IsLimit (IsAugmentation.pushforwardFork C J K u0 F) :=
  limit.isLimit
    (parallelPair (IsAugmentation.pushforwardParallel C J K u0 F 0)
      (IsAugmentation.pushforwardParallel C J K u0 F 1))

/-- Degree-zero adjoint of a map `a⁻¹ G ⟶ F`, as a map `G ⟶ a_{0,*} F_0`. -/
def IsAugmentation.homEquivToFun (G : Sheaf K.toGrothendieck (Type w))
    (F : Sheaf (topology C J) (Type w))
    (α : (IsAugmentation.inverseImage C J K u0).obj G ⟶ F) :
    G ⟶ (IsAugmentation.pushforward C J K u0).obj F :=
  equalizer.lift
    (((IsAugmentation.stageTopos C J K u0 ⦋0⦌).adjunction.homEquiv G
        (((toSheafSystem C J).obj F).obj ⦋0⦌))
      (((counitIso C J).inv.app ((IsAugmentation.inverseImageSystem C J K u0).obj G) ≫
          (toSheafSystem C J).map α).app ⦋0⦌))
    sorry

/-- Stage-`n` component of the system map associated to a map `G ⟶ a_* F`. -/
def IsAugmentation.homEquivInvFunApp (G : Sheaf K.toGrothendieck (Type w))
    (F : Sheaf (topology C J) (Type w))
    (β : G ⟶ (IsAugmentation.pushforward C J K u0).obj F) (n : SimplexCategory) :
    (IsAugmentation.stageTopos C J K u0 n)⁻¹.obj G ⟶
      ((toSheafSystem C J).obj F).obj n :=
  (IsAugmentation.stageTopos_comp C J K u0 (SimplexCategory.const ⦋0⦌ n 0)).inv.app G ≫
    (IsAugmentation.faceTopos C J (SimplexCategory.const ⦋0⦌ n 0)).inverseImage.map
      (((IsAugmentation.stageTopos C J K u0 ⦋0⦌).adjunction.homEquiv G
          (((toSheafSystem C J).obj F).obj ⦋0⦌)).symm
        (β ≫ IsAugmentation.pushforwardι C J K u0 F)) ≫
    SheafSystem.mapInverseImage ((toSheafSystem C J).obj F)
      (SimplexCategory.const ⦋0⦌ n 0)

/-- The inverse adjunction map, assembling a morphism `a⁻¹ G ⟶ F` from `G ⟶ a_* F`. -/
def IsAugmentation.homEquivInvFun (G : Sheaf K.toGrothendieck (Type w))
    (F : Sheaf (topology C J) (Type w))
    (β : G ⟶ (IsAugmentation.pushforward C J K u0).obj F) :
    (IsAugmentation.inverseImage C J K u0).obj G ⟶ F :=
  (ofSheafSystem C J).map
      (SheafSystem.homMk (IsAugmentation.homEquivInvFunApp C J K u0 G F β) sorry) ≫
    (unitIso C J).inv.app F

/-- Hom-set equivalence `Hom(a⁻¹ G, F) ≃ Hom(G, a_* F)` of the total adjunction. -/
def IsAugmentation.totalToposHomEquiv (G : Sheaf K.toGrothendieck (Type w))
    (F : Sheaf (topology C J) (Type w)) :
    ((IsAugmentation.inverseImage C J K u0).obj G ⟶ F) ≃
      (G ⟶ (IsAugmentation.pushforward C J K u0).obj F) where
  toFun := IsAugmentation.homEquivToFun C J K u0 G F
  invFun := IsAugmentation.homEquivInvFun C J K u0 G F
  left_inv := sorry
  right_inv := sorry

/-- The morphism of topoi `a : Sh(C_total) ⟶ Sh(D)` induced by the augmentation. -/
def IsAugmentation.totalTopos :
    MorphismOfTopoiIn K.toGrothendieck (topology C J) where
  inverseImageFunctor := LeftExactFunctor.of (IsAugmentation.inverseImage C J K u0)
  pushforward := IsAugmentation.pushforward C J K u0
  adjunction :=
    Adjunction.mkOfHomEquiv
      { homEquiv := IsAugmentation.totalToposHomEquiv C J K u0
        homEquiv_naturality_left_symm := sorry
        homEquiv_naturality_right := sorry }

/-- Inverse image of the total morphism is the assembled sheaf-system inverse image. -/
theorem IsAugmentation.totalTopos_inverseImage :
    (IsAugmentation.totalTopos C J K u0)⁻¹ = IsAugmentation.inverseImage C J K u0 :=
  sorry

/-- Direct image of the total morphism is the equalizer functor `a_*`. -/
theorem IsAugmentation.totalTopos_pushforward :
    (IsAugmentation.totalTopos C J K u0).pushforward =
      IsAugmentation.pushforward C J K u0 :=
  sorry

variable [∀ n, (ofStage C n).IsCocontinuous (J n).toGrothendieck (topology C J)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]

/-- Identity-on-sections identification of the degree-`n` restriction of `a⁻¹ G`
with `a_n⁻¹ G`. -/
def IsAugmentation.restrictInverseImageIso (G : Sheaf K.toGrothendieck (Type w))
    (n : SimplexCategory) :
    (restrictToDegree C J n).obj
        ((ofSheafSystem C J).obj ((IsAugmentation.inverseImageSystem C J K u0).obj G)) ≅
      (IsAugmentation.stageTopos C J K u0 n)⁻¹.obj G where
  hom := ObjectProperty.homMk { app := fun _ ↦ 𝟙 _, naturality := sorry }
  inv := ObjectProperty.homMk { app := fun _ ↦ 𝟙 _, naturality := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Inverse-image form of `a ∘ g_n = a_n`. -/
def IsAugmentation.totalTopos_comp_ofStage (n : SimplexCategory) :
    (IsAugmentation.totalTopos C J K u0)⁻¹ ⋙ (ofStageMorphism C J n)⁻¹ ≅
      (IsAugmentation.stageTopos C J K u0 n)⁻¹ :=
  NatIso.ofComponents
    (fun G ↦
      (sheafificationIso
          ((restrictToDegree C J n).obj
            ((ofSheafSystem C J).obj
              ((IsAugmentation.inverseImageSystem C J K u0).obj G)))).symm ≪≫
        IsAugmentation.restrictInverseImageIso C J K u0 G n)
    sorry

end CategoryTheory.SimplicialSites
