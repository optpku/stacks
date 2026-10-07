module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import ReasLib.CategoryTheory.Sites.Topos.TwoMorphism
public import stacks_project.Chap07.Definition_7_20_1_Cocontinuous
public import stacks_project.Chap85.Lemma_85_3_4_Fiberwise
public import stacks_project.Chap85.Lemma_85_3_5_Fiber
public import stacks_project.Chap85.Remark_85_4_1_Fiberwise

/-!
# Augmentation morphisms of topoi, fiberwise case

A cocontinuous augmentation `u0` of a fiberwise simplicial site induces stage
morphisms of topoi `a_n` and a total morphism `a : Sh(C_total) ⟶ Sh(D)` whose
inverse image is the sheaf system of the functors `a_n⁻¹` and whose direct image
is the equalizer of the two coface maps `a_{0,*} F_0 ⇉ a_{1,*} F_1`. The total
morphism is presented by the cocontinuous functor sending a degree-`n` object
`U` to `u_n(U)`.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MorphismOfTopoiIn Simplicial

noncomputable section

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : F.obj (op ⦋0⦌) ⥤ D)
variable [K.IsSite]
variable [∀ n, (J n).IsSite]
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [HasSheafify K.toGrothendieck (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [∀ (n : SimplexCategory) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor F u0 n).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck (Type w))]
variable [h_fiberwise : IsFiberwiseSite F J]
variable [h_aug : IsAugmentation F J K u0]
include h_fiberwise
include h_aug

/-- Structure-map morphism of topoi `f_φ` of the ambient fiberwise site. -/
abbrev IsAugmentation.faceTopos {m n : SimplexCategory} (φ : m ⟶ n) :
    MorphismOfTopoiIn (J (op m)).toGrothendieck (J (op n)).toGrothendieck :=
  Grothendieck.toposMap.{u, v, w} F J φ

/-- The common composite `u_n = u0 ∘ u_φ` is cocontinuous. -/
instance IsAugmentation.stageFunctor_isCocontinuous (n : SimplexCategory) :
    (IsAugmentation.stageFunctor F u0 n).IsCocontinuous
      (J (op n)).toGrothendieck K.toGrothendieck :=
  sorry

/-- Identification `u_φ ⋙ u_m ≅ u_n` of presenting functors along a simplex operator. -/
def IsAugmentation.stageFunctor_compIso {m n : SimplexCategory} (φ : m ⟶ n) :
    (F.map φ.op).toFunctor ⋙ IsAugmentation.stageFunctor F u0 m ≅
      IsAugmentation.stageFunctor F u0 n :=
  (Functor.associator (F.map φ.op).toFunctor
      ((F.map (SimplexCategory.const ⦋0⦌ m 0).op).toFunctor) u0).symm ≪≫
    NatIso.hcomp (map_comp_toFunctor F (SimplexCategory.const ⦋0⦌ m 0) φ) (Iso.refl u0) ≪≫
    eqToIso (h_aug.map_eq (SimplexCategory.const ⦋0⦌ m 0 ≫ φ)
      (SimplexCategory.const ⦋0⦌ n 0))

/-- The morphism of topoi `a_n : Sh(C_n) ⟶ Sh(D)` presented by the common
composite `u_n`. -/
def IsAugmentation.stageTopos (n : SimplexCategory) :
    MorphismOfTopoiIn K.toGrothendieck (J (op n)).toGrothendieck :=
  (IsAugmentation.stageFunctor F u0 n).morphismOfTopoiInOfCocontinuous
    (J (op n)).toGrothendieck K.toGrothendieck

/-- Inverse image of `a_n` is cocontinuous sheaf pullback along `u_n`. -/
theorem IsAugmentation.stageTopos_inverseImage (n : SimplexCategory) :
    (IsAugmentation.stageTopos F J K u0 n)⁻¹ =
      (IsAugmentation.stageFunctor F u0 n).sheafPullbackCocontinuous (Type w)
        (J (op n)).toGrothendieck K.toGrothendieck :=
  sorry

/-- Direct image of `a_n` is cocontinuous sheaf pushforward along `u_n`. -/
theorem IsAugmentation.stageTopos_pushforward (n : SimplexCategory) :
    (IsAugmentation.stageTopos F J K u0 n).pushforward =
      (IsAugmentation.stageFunctor F u0 n).sheafPushforwardCocontinuous (Type w)
        (J (op n)).toGrothendieck K.toGrothendieck :=
  sorry

/-- Inverse-image form of `a_m ∘ f_φ = a_n`. -/
def IsAugmentation.stageTopos_comp {m n : SimplexCategory} (φ : m ⟶ n) :
    (IsAugmentation.stageTopos F J K u0 m)⁻¹ ⋙ (IsAugmentation.faceTopos F J φ)⁻¹ ≅
      (IsAugmentation.stageTopos F J K u0 n)⁻¹ :=
  Adjunction.leftAdjointUniq
    ((Adjunction.comp
        ((IsAugmentation.stageFunctor F u0 m).sheafPullbackCocontinuousAdjunction
          (J (op m)).toGrothendieck K.toGrothendieck)
        ((F.map φ.op).toFunctor.sheafPullbackCocontinuousAdjunction
          (J (op n)).toGrothendieck (J (op m)).toGrothendieck)).ofNatIsoRight
      (Functor.sheafPushforwardCocontinuousComp'
        (J (op n)).toGrothendieck (J (op m)).toGrothendieck K.toGrothendieck
        (F.map φ.op).toFunctor (IsAugmentation.stageFunctor F u0 m)
        (IsAugmentation.stageFunctor_compIso F J K u0 φ)))
    ((IsAugmentation.stageFunctor F u0 n).sheafPullbackCocontinuousAdjunction
      (J (op n)).toGrothendieck K.toGrothendieck)

/-- Direct-image mate of `a_m ∘ f_φ = a_n`. -/
def IsAugmentation.stageTopos_pushforward_comp {m n : SimplexCategory} (φ : m ⟶ n) :
    (IsAugmentation.faceTopos F J φ).pushforward ⋙ (IsAugmentation.stageTopos F J K u0 m).pushforward ≅
      (IsAugmentation.stageTopos F J K u0 n).pushforward :=
  MorphismOfTopoiIn.pushforwardIsoOfInverseImageIso
    (MorphismOfTopoiIn.comp (IsAugmentation.stageTopos F J K u0 m) (IsAugmentation.faceTopos F J φ))
    (IsAugmentation.stageTopos F J K u0 n)
    (IsAugmentation.stageTopos_comp F J K u0 φ)

/-- Pushforward-form transition of the inverse-image sheaf system at a simplex operator. -/
def IsAugmentation.inverseImageSystemMap (G : Sheaf K.toGrothendieck (Type w))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (IsAugmentation.stageTopos F J K u0 m)⁻¹.obj G ⟶
      (IsAugmentation.faceTopos F J φ).pushforward.obj
        ((IsAugmentation.stageTopos F J K u0 n)⁻¹.obj G) :=
  ((IsAugmentation.faceTopos F J φ).adjunction.homEquiv
      ((IsAugmentation.stageTopos F J K u0 m)⁻¹.obj G)
      ((IsAugmentation.stageTopos F J K u0 n)⁻¹.obj G))
    ((IsAugmentation.stageTopos_comp F J K u0 φ).hom.app G)

/-- The sheaf system whose stage sheaves are `a_n⁻¹ G` and whose transitions are the
identifications `f_φ⁻¹ a_m⁻¹ G ≅ a_n⁻¹ G`. -/
def IsAugmentation.inverseImageSystem :
    Sheaf K.toGrothendieck (Type w) ⥤
      SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck)
        (fun φ ↦ IsAugmentation.faceTopos F J φ) where
  obj G :=
    SimplicialSites.SheafSystem.of
      (fun n ↦ (IsAugmentation.stageTopos F J K u0 n)⁻¹.obj G)
      (fun {m n} φ ↦ IsAugmentation.inverseImageSystemMap F J K u0 G φ) sorry sorry
  map {G H} α :=
    SimplicialSites.SheafSystem.homMk
      (fun n ↦ (IsAugmentation.stageTopos F J K u0 n)⁻¹.map α) sorry
  map_id := sorry
  map_comp := sorry

/-- The stage sheaf of `inverseImageSystem.obj G` at `n` is `a_n⁻¹ G`. -/
theorem IsAugmentation.inverseImageSystem_obj (G : Sheaf K.toGrothendieck (Type w))
    (n : SimplexCategory) :
    ((IsAugmentation.inverseImageSystem F J K u0).obj G).obj n =
      (IsAugmentation.stageTopos F J K u0 n)⁻¹.obj G :=
  sorry

/-- Inverse image `a⁻¹` of the total augmentation morphism. -/
def IsAugmentation.inverseImage :
    Sheaf K.toGrothendieck (Type w) ⥤ Sheaf (topology F J) (Type w) :=
  IsAugmentation.inverseImageSystem F J K u0 ⋙ ofSheafSystem F J

/-- Inverse image of a sheaf `G` is `ofSheafSystem` of the system of the sheaves `a_n⁻¹ G`. -/
theorem IsAugmentation.inverseImage_obj (G : Sheaf K.toGrothendieck (Type w)) :
    (IsAugmentation.inverseImage F J K u0).obj G =
      (ofSheafSystem F J).obj ((IsAugmentation.inverseImageSystem F J K u0).obj G) :=
  sorry

/-- Inverse image `a⁻¹` preserves finite limits. -/
instance IsAugmentation.inverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (IsAugmentation.inverseImage F J K u0) :=
  sorry

/-- The two maps `a_{0,*} F_0 ⇉ a_{1,*} F_1` induced by the coface operators `δ i`. -/
def IsAugmentation.pushforwardParallel (G : Sheaf (topology F J) (Type w)) (i : Fin 2) :
    (IsAugmentation.stageTopos F J K u0 ⦋0⦌).pushforward.obj
      (((toSheafSystem F J).obj G).obj ⦋0⦌) ⟶
      (IsAugmentation.stageTopos F J K u0 ⦋1⦌).pushforward.obj
        (((toSheafSystem F J).obj G).obj ⦋1⦌) :=
  (IsAugmentation.stageTopos F J K u0 ⦋0⦌).pushforward.map
      ((IsAugmentation.faceTopos F J (SimplexCategory.δ i : ⦋0⦌ ⟶ ⦋1⦌)).adjunction.unit.app
        (((toSheafSystem F J).obj G).obj ⦋0⦌)) ≫
    (IsAugmentation.stageTopos F J K u0 ⦋0⦌).pushforward.map
      ((IsAugmentation.faceTopos F J (SimplexCategory.δ i : ⦋0⦌ ⟶ ⦋1⦌)).pushforward.map
        (SimplicialSites.SheafSystem.mapInverseImage ((toSheafSystem F J).obj G)
          (SimplexCategory.δ i : ⦋0⦌ ⟶ ⦋1⦌))) ≫
    (IsAugmentation.stageTopos_pushforward_comp F J K u0
        (SimplexCategory.δ i : ⦋0⦌ ⟶ ⦋1⦌)).hom.app
      (((toSheafSystem F J).obj G).obj ⦋1⦌)

/-- Direct image `a_*`, sending a sheaf on `C_total` to the equalizer of
`a_{0,*} F_0 ⇉ a_{1,*} F_1`. -/
def IsAugmentation.pushforward :
    Sheaf (topology F J) (Type w) ⥤ Sheaf K.toGrothendieck (Type w) where
  obj G :=
    equalizer (IsAugmentation.pushforwardParallel F J K u0 G 0)
      (IsAugmentation.pushforwardParallel F J K u0 G 1)
  map {G H} α :=
    equalizer.lift
      (equalizer.ι (IsAugmentation.pushforwardParallel F J K u0 G 0)
          (IsAugmentation.pushforwardParallel F J K u0 G 1) ≫
        (IsAugmentation.stageTopos F J K u0 ⦋0⦌).pushforward.map
          (((toSheafSystem F J).map α).app ⦋0⦌))
      sorry
  map_id := sorry
  map_comp := sorry

/-- The object `a_* G` is the equalizer of the two coface maps. -/
theorem IsAugmentation.pushforward_obj (G : Sheaf (topology F J) (Type w)) :
    (IsAugmentation.pushforward F J K u0).obj G =
      equalizer (IsAugmentation.pushforwardParallel F J K u0 G 0)
        (IsAugmentation.pushforwardParallel F J K u0 G 1) :=
  sorry

/-- The comparison `a_* G ⟶ a_{0,*} G_0`. -/
def IsAugmentation.pushforwardι (G : Sheaf (topology F J) (Type w)) :
    (IsAugmentation.pushforward F J K u0).obj G ⟶
      (IsAugmentation.stageTopos F J K u0 ⦋0⦌).pushforward.obj
        (((toSheafSystem F J).obj G).obj ⦋0⦌) :=
  equalizer.ι (IsAugmentation.pushforwardParallel F J K u0 G 0)
    (IsAugmentation.pushforwardParallel F J K u0 G 1)

/-- The fork presenting `a_* G` as equalizer of `a_{0,*} G_0 ⇉ a_{1,*} G_1`. -/
def IsAugmentation.pushforwardFork (G : Sheaf (topology F J) (Type w)) :
    Fork (IsAugmentation.pushforwardParallel F J K u0 G 0)
      (IsAugmentation.pushforwardParallel F J K u0 G 1) :=
  equalizer.fork (IsAugmentation.pushforwardParallel F J K u0 G 0)
    (IsAugmentation.pushforwardParallel F J K u0 G 1)

/-- The two coface maps coequalize `pushforwardι`. -/
theorem IsAugmentation.pushforwardFork_condition (G : Sheaf (topology F J) (Type w)) :
    IsAugmentation.pushforwardι F J K u0 G ≫
        IsAugmentation.pushforwardParallel F J K u0 G 0 =
      IsAugmentation.pushforwardι F J K u0 G ≫
        IsAugmentation.pushforwardParallel F J K u0 G 1 :=
  sorry

/-- The mediating morphism into `a_* G` from a test cone. -/
def IsAugmentation.pushforwardForkLift (G : Sheaf (topology F J) (Type w))
    (s : Fork (IsAugmentation.pushforwardParallel F J K u0 G 0)
      (IsAugmentation.pushforwardParallel F J K u0 G 1)) :
    s.pt ⟶ (IsAugmentation.pushforward F J K u0).obj G :=
  equalizer.lift (Fork.ι s) sorry

/-- `a_* G` is the equalizer of the two maps `a_{0,*} G_0 ⇉ a_{1,*} G_1`. -/
def IsAugmentation.pushforwardFork_isLimit (G : Sheaf (topology F J) (Type w)) :
    IsLimit (IsAugmentation.pushforwardFork F J K u0 G) :=
  limit.isLimit
    (parallelPair (IsAugmentation.pushforwardParallel F J K u0 G 0)
      (IsAugmentation.pushforwardParallel F J K u0 G 1))

/-- Degree-zero adjoint of a map `a⁻¹ H ⟶ G`, as a map `H ⟶ a_{0,*} G_0`. -/
def IsAugmentation.homEquivToFun (H : Sheaf K.toGrothendieck (Type w))
    (G : Sheaf (topology F J) (Type w))
    (α : (IsAugmentation.inverseImage F J K u0).obj H ⟶ G) :
    H ⟶ (IsAugmentation.pushforward F J K u0).obj G :=
  equalizer.lift
    (((IsAugmentation.stageTopos F J K u0 ⦋0⦌).adjunction.homEquiv H
        (((toSheafSystem F J).obj G).obj ⦋0⦌))
      (((counitIso F J).inv.app ((IsAugmentation.inverseImageSystem F J K u0).obj H) ≫
          (toSheafSystem F J).map α).app ⦋0⦌))
    sorry

/-- Stage-`n` component of the system map associated to a map `H ⟶ a_* G`. -/
def IsAugmentation.homEquivInvFunApp (H : Sheaf K.toGrothendieck (Type w))
    (G : Sheaf (topology F J) (Type w))
    (β : H ⟶ (IsAugmentation.pushforward F J K u0).obj G) (n : SimplexCategory) :
    (IsAugmentation.stageTopos F J K u0 n)⁻¹.obj H ⟶
      ((toSheafSystem F J).obj G).obj n :=
  (IsAugmentation.stageTopos_comp F J K u0 (SimplexCategory.const ⦋0⦌ n 0)).inv.app H ≫
    (IsAugmentation.faceTopos F J (SimplexCategory.const ⦋0⦌ n 0)).inverseImage.map
      (((IsAugmentation.stageTopos F J K u0 ⦋0⦌).adjunction.homEquiv H
          (((toSheafSystem F J).obj G).obj ⦋0⦌)).symm
        (β ≫ IsAugmentation.pushforwardι F J K u0 G)) ≫
    SimplicialSites.SheafSystem.mapInverseImage ((toSheafSystem F J).obj G)
      (SimplexCategory.const ⦋0⦌ n 0)

/-- The inverse adjunction map, assembling a morphism `a⁻¹ H ⟶ G` from `H ⟶ a_* G`. -/
def IsAugmentation.homEquivInvFun (H : Sheaf K.toGrothendieck (Type w))
    (G : Sheaf (topology F J) (Type w))
    (β : H ⟶ (IsAugmentation.pushforward F J K u0).obj G) :
    (IsAugmentation.inverseImage F J K u0).obj H ⟶ G :=
  (ofSheafSystem F J).map
      (SimplicialSites.SheafSystem.homMk
        (IsAugmentation.homEquivInvFunApp F J K u0 H G β) sorry) ≫
    (unitIso F J).inv.app G

/-- Hom-set equivalence `Hom(a⁻¹ H, G) ≃ Hom(H, a_* G)` of the total adjunction. -/
def IsAugmentation.totalToposHomEquiv (H : Sheaf K.toGrothendieck (Type w))
    (G : Sheaf (topology F J) (Type w)) :
    ((IsAugmentation.inverseImage F J K u0).obj H ⟶ G) ≃
      (H ⟶ (IsAugmentation.pushforward F J K u0).obj G) where
  toFun := IsAugmentation.homEquivToFun F J K u0 H G
  invFun := IsAugmentation.homEquivInvFun F J K u0 H G
  left_inv := sorry
  right_inv := sorry

/-- The morphism of topoi `a : Sh(C_total) ⟶ Sh(D)` induced by the augmentation. -/
def IsAugmentation.totalTopos :
    MorphismOfTopoiIn K.toGrothendieck (topology F J) where
  inverseImageFunctor := LeftExactFunctor.of (IsAugmentation.inverseImage F J K u0)
  pushforward := IsAugmentation.pushforward F J K u0
  adjunction :=
    Adjunction.mkOfHomEquiv
      { homEquiv := IsAugmentation.totalToposHomEquiv F J K u0
        homEquiv_naturality_left_symm := sorry
        homEquiv_naturality_right := sorry }

/-- Inverse image of the total morphism is the assembled sheaf-system inverse image. -/
theorem IsAugmentation.totalTopos_inverseImage :
    (IsAugmentation.totalTopos F J K u0)⁻¹ = IsAugmentation.inverseImage F J K u0 :=
  sorry

/-- Direct image of the total morphism is the equalizer functor `a_*`. -/
theorem IsAugmentation.totalTopos_pushforward :
    (IsAugmentation.totalTopos F J K u0).pushforward =
      IsAugmentation.pushforward F J K u0 :=
  sorry

/-- The presenting functor `C_total ⥤ D` sending a degree-`n` object `U` to `u_n(U)`. -/
def IsAugmentation.totalFunctor : Grothendieck F ⥤ D where
  obj X := (IsAugmentation.stageFunctor F u0 X.base.unop).obj X.fiber
  map {X Y} f :=
    (IsAugmentation.stageFunctor_compIso F J K u0 f.base.unop).inv.app X.fiber ≫
      (IsAugmentation.stageFunctor F u0 Y.base.unop).map f.fiber
  map_id := sorry
  map_comp := sorry

/-- On a degree-`n` object `U`, the presenting functor is `u_n(U)`. -/
theorem IsAugmentation.totalFunctor_obj (n : SimplexCategory) (U : F.obj (op n)) :
    (IsAugmentation.totalFunctor F J K u0).obj ⟨op n, U⟩ =
      (IsAugmentation.stageFunctor F u0 n).obj U :=
  sorry

/-- The presenting functor of the total morphism is cocontinuous. -/
instance IsAugmentation.totalFunctor_isCocontinuous :
    (IsAugmentation.totalFunctor F J K u0).IsCocontinuous
      (topology F J) K.toGrothendieck :=
  sorry

variable [∀ n, (ι F (op n)).IsCocontinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]

/-- Identity-on-sections identification of the degree-`n` restriction of `a⁻¹ H`
with `a_n⁻¹ H`. -/
def IsAugmentation.restrictInverseImageIso (H : Sheaf K.toGrothendieck (Type w))
    (n : SimplexCategory) :
    (restrictToDegree F J n).obj
        ((ofSheafSystem F J).obj ((IsAugmentation.inverseImageSystem F J K u0).obj H)) ≅
      (IsAugmentation.stageTopos F J K u0 n)⁻¹.obj H where
  hom := ObjectProperty.homMk { app := fun _ ↦ 𝟙 _, naturality := sorry }
  inv := ObjectProperty.homMk { app := fun _ ↦ 𝟙 _, naturality := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Inverse-image form of `a ∘ g_n = a_n`. -/
def IsAugmentation.totalTopos_comp_fiberMorphism (n : SimplexCategory) :
    (IsAugmentation.totalTopos F J K u0)⁻¹ ⋙ (fiberMorphism F J n)⁻¹ ≅
      (IsAugmentation.stageTopos F J K u0 n)⁻¹ :=
  NatIso.ofComponents
    (fun H ↦
      (sheafificationIso
          ((restrictToDegree F J n).obj
            ((ofSheafSystem F J).obj
              ((IsAugmentation.inverseImageSystem F J K u0).obj H)))).symm ≪≫
        IsAugmentation.restrictInverseImageIso F J K u0 H n)
    sorry

end CategoryTheory.Grothendieck
