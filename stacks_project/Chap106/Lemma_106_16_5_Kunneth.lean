module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.Groupoids.UnderlyingFunctorIso
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.BaseChange
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import stacks_project.Chap103.Proposition_103_11_1
public import stacks_project.Chap103.Remark_103_11_3_CupProduct

/-!
# Quasi-coherent Künneth comparison for structure sheaves

The underived Künneth morphism of quasi-coherent structure sheaves along a pair
of quasi-compact quasi-separated morphisms of algebraic stacks, assembled from
relative pullback maps, the quasi-coherent tensor, and multiplication of
structure sheaves.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Adjunction
open AlgebraicGeometry.AlgebraicStack AlgebraicGeometry.GroupoidsOver
open CategoryTheory.MonoidalCategory CategoryTheory.ObjectProperty
open FiberedCategoryOver.Groupoids
open SheafOfModules.RingedSite
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The cartesian total functor of a 1-morphism agrees with `toFunctor`. -/
theorem toCartesian_toFunctor_eq {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    (toCartesianBasedFunctor h).toFunctor = toFunctor h :=
  sorry

/-- The cartesian total functors of `f` and `g` compose to the cartesian total
functor of the composite, after identifying each with `toFunctor`. -/
def cartesianToFunctor_functorComp {X Y Z : GroupoidsOver S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (toCartesianBasedFunctor f).toFunctor ⋙ (toCartesianBasedFunctor g).toFunctor ≅
      (toCartesianBasedFunctor (f ≫ g)).toFunctor :=
  eqToIso
      (congrArg₂ (fun F G ↦ F ⋙ G) (toCartesian_toFunctor_eq f)
        (toCartesian_toFunctor_eq g)) ≪≫
    FullSubbicategory.toFunctor.compIso f g ≪≫
      eqToIso (toCartesian_toFunctor_eq (f ≫ g)).symm

/-- Composite of cartesian total functors is continuous for inherited fppf
topologies. -/
instance cartesianToFunctor_functorComp_isContinuous {X Y Z : GroupoidsOver S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((toCartesianBasedFunctor f).toFunctor ⋙
        (toCartesianBasedFunctor g).toFunctor).IsContinuous
      (inheritedFppfTopology X) (inheritedFppfTopology Z) :=
  sorry

/-- The cartesian total functor of `h₂` transported along `toFunctorIso e`
agrees with the cartesian total functor of `h₁`. -/
def cartesianToFunctor_isoOfIso {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y}
    (e : h₁ ≅ h₂) :
    (toCartesianBasedFunctor h₁).toFunctor ≅ (toCartesianBasedFunctor h₂).toFunctor :=
  eqToIso (toCartesian_toFunctor_eq h₁) ≪≫ toFunctorIso e ≪≫
    (eqToIso (toCartesian_toFunctor_eq h₂)).symm

/-- The composite structure-sheaf map along cartesian total functors of `f` and
`g`. -/
def modulePullbackCompData {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    structureSheaf X ⟶
      (((toCartesianBasedFunctor f).toFunctor ⋙
          (toCartesianBasedFunctor g).toFunctor).sheafPushforwardContinuous
        RingCat.{u} (inheritedFppfTopology X) (inheritedFppfTopology Z)).obj
        (structureSheaf Z) :=
  structureSheafMap f ≫
    ((toCartesianBasedFunctor f).toFunctor.sheafPushforwardContinuous RingCat.{u}
        (inheritedFppfTopology X) (inheritedFppfTopology Y)).map (structureSheafMap g)

/-- Module inverse image along a composite, before transporting the total
functor. -/
def modulePullbackComp₀ {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullback g ⋙ modulePullback f ≅
      SheafOfModules.pushforward (modulePullbackCompData f g) :=
  SheafOfModules.pushforwardComp (structureSheafMap f) (structureSheafMap g)

/-- Transport of composite inverse image along the cartesian total-functor
composition isomorphism. -/
def modulePullbackComp₁ {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    SheafOfModules.pushforward (modulePullbackCompData f g) ≅
      SheafOfModules.pushforward
        (modulePullbackCompData f g ≫
          (Functor.sheafPushforwardContinuousNatTrans
              (cartesianToFunctor_functorComp f g).hom RingCat.{u}
              (inheritedFppfTopology X) (inheritedFppfTopology Z)).app
            (structureSheaf Z)) :=
  SheafOfModules.pushforwardNatIso (modulePullbackCompData f g)
    (cartesianToFunctor_functorComp f g)

/-- The transported composite structure-sheaf map agrees with the structure-sheaf
map of the composite 1-morphism. -/
theorem structureSheafMap_functorComp {X Y Z : GroupoidsOver S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullbackCompData f g ≫
        (Functor.sheafPushforwardContinuousNatTrans
            (cartesianToFunctor_functorComp f g).hom RingCat.{u}
            (inheritedFppfTopology X) (inheritedFppfTopology Z)).app
          (structureSheaf Z) =
      structureSheafMap (f ≫ g) :=
  sorry

/-- Align the transported composite inverse image with inverse image along the
composite. -/
def modulePullbackComp₂ {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    SheafOfModules.pushforward
        (modulePullbackCompData f g ≫
          (Functor.sheafPushforwardContinuousNatTrans
              (cartesianToFunctor_functorComp f g).hom RingCat.{u}
              (inheritedFppfTopology X) (inheritedFppfTopology Z)).app
            (structureSheaf Z)) ≅
      modulePullback (f ≫ g) :=
  SheafOfModules.pushforwardCongr (structureSheafMap_functorComp f g)

/-- Inverse image of modules along a composite 1-morphism is the composite of
the inverse images. -/
def modulePullbackComp {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullback g ⋙ modulePullback f ≅ modulePullback (f ≫ g) :=
  modulePullbackComp₀ f g ≪≫ modulePullbackComp₁ f g ≪≫ modulePullbackComp₂ f g

/-- Transport of inverse image along the real total-functor isomorphism. -/
def modulePullbackWhisker₀ {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (e : h₁ ≅ h₂) :
    modulePullback h₂ ≅
      SheafOfModules.pushforward
        (structureSheafMap h₂ ≫
          (Functor.sheafPushforwardContinuousNatTrans
              (cartesianToFunctor_isoOfIso e).hom RingCat.{u}
              (inheritedFppfTopology X) (inheritedFppfTopology Y)).app
            (structureSheaf Y)) :=
  SheafOfModules.pushforwardNatIso (structureSheafMap h₂)
    (cartesianToFunctor_isoOfIso e)

/-- The structure-sheaf map of `h₂` transported along
`cartesianToFunctor_isoOfIso e` agrees with the structure-sheaf map of `h₁`. -/
theorem structureSheafMap_isoOfIso {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y}
    (e : h₁ ≅ h₂) :
    structureSheafMap h₂ ≫
        (Functor.sheafPushforwardContinuousNatTrans
            (cartesianToFunctor_isoOfIso e).hom RingCat.{u}
            (inheritedFppfTopology X) (inheritedFppfTopology Y)).app
          (structureSheaf Y) =
      structureSheafMap h₁ :=
  sorry

/-- Align the transported inverse image with inverse image along `h₁`. -/
def modulePullbackWhisker₁ {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (e : h₁ ≅ h₂) :
    SheafOfModules.pushforward
        (structureSheafMap h₂ ≫
          (Functor.sheafPushforwardContinuousNatTrans
              (cartesianToFunctor_isoOfIso e).hom RingCat.{u}
              (inheritedFppfTopology X) (inheritedFppfTopology Y)).app
            (structureSheaf Y)) ≅
      modulePullback h₁ :=
  SheafOfModules.pushforwardCongr (structureSheafMap_isoOfIso e)

/-- A 2-isomorphism of 1-morphisms induces an isomorphism of module inverse
images. -/
def modulePullbackWhisker {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (e : h₁ ≅ h₂) :
    modulePullback h₁ ≅ modulePullback h₂ :=
  (modulePullbackWhisker₀ e ≪≫ modulePullbackWhisker₁ e).symm

namespace QCoh

/-- The quasi-coherent structure sheaf `O_X` of an algebraic stack, as the unit
module on the fppf ringed site. -/
def structureSheaf (X : GroupoidsOver S) [AlgebraicStack X] : QCoh X where
  obj := SheafOfModules.unit (fppfRingedSite X).structureSheaf
  property := sorry

/-- The underlying module of `structureSheaf X` is the unit on the fppf ringed
site of `X`. -/
theorem structureSheaf_obj (X : GroupoidsOver S) [AlgebraicStack X] :
    (structureSheaf X).obj = SheafOfModules.unit (fppfRingedSite X).structureSheaf :=
  sorry

/-- The obvious morphism `f : Y ×_X Z ⟶ X` from the chosen 2-fibre product,
as `TwoFibreProduct.fst a b ≫ a`. -/
abbrev fibreProductHom {X Y Z : GroupoidsOver S} (a : Y ⟶ X) (b : Z ⟶ X) :
    TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b ⟶ X :=
  TwoFibreProduct.fst.{u + 1, u, u + 1, u} a b ≫ a

/-- `fibreProductHom a b` is the composite of the first 2-fibre-product
projection with `a`. -/
theorem fibreProductHom_eq {X Y Z : GroupoidsOver S} (a : Y ⟶ X) (b : Z ⟶ X) :
    fibreProductHom a b = TwoFibreProduct.fst.{u + 1, u, u + 1, u} a b ≫ a :=
  sorry

/-- The canonical 2-isomorphism identifying the two composites from the chosen
2-fibre product to `X`. -/
def fibreProductHom_comparison {X Y Z : GroupoidsOver S} (a : Y ⟶ X) (b : Z ⟶ X) :
    fibreProductHom a b ≅
      TwoFibreProduct.snd.{u + 1, u, u + 1, u} a b ≫ b :=
  TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} a b

/-- `fibreProductHom_comparison a b` is the chosen 2-fibre-product comparison
cell. -/
theorem fibreProductHom_comparison_eq {X Y Z : GroupoidsOver S}
    (a : Y ⟶ X) (b : Z ⟶ X) :
    fibreProductHom_comparison a b =
      TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} a b :=
  sorry

/-- The coefficient map `O_X ⟶ f^{-1} O_Y` induces a morphism from the
quasi-coherent structure sheaf of `X` to the pullback of the structure sheaf of
`Y`. -/
def structureSheafPullbackHom {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    structureSheaf X ⟶ (pullback f).obj (structureSheaf Y) :=
  homMk (SheafOfModules.unitToPushforwardObjUnit (structureSheafMap f))

/-- `structureSheafPullbackHom f` is `unitToPushforwardObjUnit` of
`structureSheafMap f`. -/
theorem structureSheafPullbackHom_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    structureSheafPullbackHom f =
      homMk (SheafOfModules.unitToPushforwardObjUnit (structureSheafMap f)) :=
  sorry

/-- Pullback of quasi-coherent structure sheaves along a 1-morphism is an
isomorphism, because `structureSheafMap` is an isomorphism. -/
instance structureSheafPullbackHom_isIso {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    IsIso (structureSheafPullbackHom f) :=
  sorry

/-- The module-level inverse of `structureSheafPullbackHom`, obtained from
`structureSheafIso.hom` rather than `inv` of a deferred `IsIso`. -/
def structureSheafPullbackInv_module {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    ((pullback f).obj (structureSheaf Y)).obj ⟶ (structureSheaf X).obj where
  val.app x :=
    ModuleCat.homMk
      ((forget₂ RingCat.{u} AddCommGrpCat.{u}).map
        ((structureSheafIso f).hom.hom.app x))
      sorry
  val.naturality := sorry

/-- Inverse of `structureSheafPullbackHom`, as the quasi-coherent map associated
to `structureSheafIso`. -/
def structureSheafPullbackInv {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    (pullback f).obj (structureSheaf Y) ⟶ structureSheaf X :=
  homMk (structureSheafPullbackInv_module f)

/-- `structureSheafPullbackInv f` is the quasi-coherent packaging of
`structureSheafPullbackInv_module f`. -/
theorem structureSheafPullbackInv_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    structureSheafPullbackInv f = homMk (structureSheafPullbackInv_module f) :=
  sorry

/-- Comparison of the transported structure sheaf with the tensor unit of
commutative fppf modules. -/
def structureSheafCommUnitToTensorUnit (X : GroupoidsOver S) [AlgebraicStack X] :
    (toCommFppfModules X).obj (structureSheaf X).obj ⟶ 𝟙_ (commFppfModules X) :=
  unitModuleToTensorUnit (J := inheritedFppfTopology X) (𝒪 := commFppfStructureSheaf X)

/-- Comparison of the tensor unit of commutative fppf modules with the
transported structure sheaf. -/
def tensorUnitToStructureSheafCommUnit (X : GroupoidsOver S) [AlgebraicStack X] :
    𝟙_ (commFppfModules X) ⟶ (toCommFppfModules X).obj (structureSheaf X).obj :=
  tensorUnitToUnitModule (J := inheritedFppfTopology X) (𝒪 := commFppfStructureSheaf X)

/-- Recover a fppf module from its commutative presentation. -/
def fromToCommFppfModulesHom {X : GroupoidsOver S}
    (F : RingedSite.ModuleCat.{u} (fppfRingedSite X)) :
    (fromCommFppfModules X).obj ((toCommFppfModules X).obj F) ⟶ F :=
  ⟨(PresheafOfModules.Restriction.compComponentIso'
        (fromCommFppfCoefficient X) (toCommFppfCoefficient X)
        (𝟙 (AlgebraicGeometry.GroupoidsOver.structureSheaf X).obj)
        (fromCommFppfCoefficient_comp_toCommFppfCoefficient X) F.val).hom ≫
      (PresheafOfModules.Restriction.idComponentIso'
        (𝟙 (AlgebraicGeometry.GroupoidsOver.structureSheaf X).obj) rfl F.val).hom⟩

/-- Multiplication of the quasi-coherent structure sheaf, obtained from the left
unitor of the commutative fppf tensor at the tensor unit. -/
def structureSheafMul (X : GroupoidsOver S) [AlgebraicStack X] :
    tensor (structureSheaf X) (structureSheaf X) ⟶ structureSheaf X :=
  homMk
    ((fromCommFppfModules X).map
        (moduleTensorMap.{u + 1, u, u}
            (structureSheafCommUnitToTensorUnit X)
            (structureSheafCommUnitToTensorUnit X) ≫
          (λ_ (𝟙_ (commFppfModules X))).hom ≫
            tensorUnitToStructureSheafCommUnit X) ≫
      fromToCommFppfModulesHom (structureSheaf X).obj)

/-- `structureSheafMul X` is the transported left unitor of the commutative
fppf tensor at the unit. -/
theorem structureSheafMul_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    structureSheafMul X =
      homMk
        ((fromCommFppfModules X).map
            (moduleTensorMap.{u + 1, u, u}
                (structureSheafCommUnitToTensorUnit X)
                (structureSheafCommUnitToTensorUnit X) ≫
              (λ_ (𝟙_ (commFppfModules X))).hom ≫
                tensorUnitToStructureSheafCommUnit X) ≫
          fromToCommFppfModulesHom (structureSheaf X).obj) :=
  sorry

/-- Restriction of module inverse-image composition to quasi-coherent
pullbacks. -/
def qcohPullback_functorComp {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  NatIso.ofComponents
    (fun F ↦
      (quasiCoherentModuleProperty X).isoMk
        ((FullSubcategory.restrict.compιIso (modulePullback (f ≫ g))
            (modulePullback_le_inverseImage (f ≫ g))).app F ≪≫
          ((modulePullbackComp f g).app F.obj).symm ≪≫
            (modulePullback f).mapIso
              ((FullSubcategory.restrict.compιIso (modulePullback g)
                  (modulePullback_le_inverseImage g)).symm.app F) ≪≫
              (FullSubcategory.restrict.compιIso (modulePullback f)
                  (modulePullback_le_inverseImage f)).symm.app
                ((pullback g).obj F)))
    sorry

/-- Restriction of a 2-isomorphism of 1-morphisms to quasi-coherent pullbacks. -/
def qcohPullback_isoOfIso {X Y : GroupoidsOver S} {f g : X ⟶ Y} (e : f ≅ g) :
    pullback g ≅ pullback f :=
  NatIso.ofComponents
    (fun F ↦
      (quasiCoherentModuleProperty X).isoMk
        ((FullSubcategory.restrict.compιIso (modulePullback g)
            (modulePullback_le_inverseImage g)).app F ≪≫
          ((modulePullbackWhisker e).app F.obj).symm ≪≫
            (FullSubcategory.restrict.compιIso (modulePullback f)
                (modulePullback_le_inverseImage f)).symm.app F))
    sorry

/-- The 2-cell `𝟭 ⋙ pullback f ≅ pullback a ⋙ pullback fst` of the triangle
`fst ≫ a = f`. -/
def kunnethPullbackSquare {X Y Z : GroupoidsOver S}
    (a : Y ⟶ X) (b : Z ⟶ X) :
    𝟭 (QCoh X) ⋙ pullback (fibreProductHom a b) ≅
      pullback a ⋙
        pullback (TwoFibreProduct.fst.{u + 1, u, u + 1, u} a b) :=
  (pullback (fibreProductHom a b)).leftUnitor ≪≫
    qcohPullback_functorComp (TwoFibreProduct.fst.{u + 1, u, u + 1, u} a b) a

/-- The 2-cell `𝟭 ⋙ pullback f ≅ pullback b ⋙ pullback snd` obtained by
transporting along the 2-fibre-product comparison isomorphism. -/
def kunnethPullbackSquare_right {X Y Z : GroupoidsOver S}
    (a : Y ⟶ X) (b : Z ⟶ X) :
    𝟭 (QCoh X) ⋙ pullback (fibreProductHom a b) ≅
      pullback b ⋙
        pullback (TwoFibreProduct.snd.{u + 1, u, u + 1, u} a b) :=
  (pullback (fibreProductHom a b)).leftUnitor ≪≫
    (qcohPullback_isoOfIso (fibreProductHom_comparison a b)).symm ≪≫
      qcohPullback_functorComp (TwoFibreProduct.snd.{u + 1, u, u + 1, u} a b) b

variable {X Y Z : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
variable (a : Y ⟶ X) (b : Z ⟶ X)
variable [AlgebraicStack.QuasiCompact a] [AlgebraicStack.QuasiSeparated a]
variable [AlgebraicStack.QuasiCompact b] [AlgebraicStack.QuasiSeparated b]
variable [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b)]
variable [AlgebraicStack.QuasiCompact (fibreProductHom a b)]
variable [AlgebraicStack.QuasiSeparated (fibreProductHom a b)]

/-- Relative pullback map `a_{QCoh,*} O_Y ⟶ f_{QCoh,*} fst^* O_Y` induced by the
triangle `fst ≫ a = f`. -/
def relativePullbackMap :
    (directImage a).obj (structureSheaf Y) ⟶
      (directImage (fibreProductHom a b)).obj
        ((pullback (TwoFibreProduct.fst.{u + 1, u, u + 1, u} a b)).obj
          (structureSheaf Y)) :=
  DerivedBaseChange.app
    (pullback_directImage_adjunction a).some
    (pullback_directImage_adjunction (fibreProductHom a b)).some
    (kunnethPullbackSquare a b) (structureSheaf Y)

/-- Relative pullback map `b_{QCoh,*} O_Z ⟶ f_{QCoh,*} snd^* O_Z` induced by the
triangle `snd ≫ b ≅ f`. -/
def relativePullbackMap_right :
    (directImage b).obj (structureSheaf Z) ⟶
      (directImage (fibreProductHom a b)).obj
        ((pullback (TwoFibreProduct.snd.{u + 1, u, u + 1, u} a b)).obj
          (structureSheaf Z)) :=
  DerivedBaseChange.app
    (pullback_directImage_adjunction b).some
    (pullback_directImage_adjunction (fibreProductHom a b)).some
    (kunnethPullbackSquare_right a b) (structureSheaf Z)

/-- Relative structure-sheaf pushforward
`a_{QCoh,*} O_Y ⟶ f_{QCoh,*} O_{Y ×_X Z}` obtained from the relative pullback
map and `structureSheafPullbackInv`. -/
def relativeStructurePushforward :
    (directImage a).obj (structureSheaf Y) ⟶
      (directImage (fibreProductHom a b)).obj
        (structureSheaf (TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b)) :=
  relativePullbackMap a b ≫
    (directImage (fibreProductHom a b)).map
      (structureSheafPullbackInv
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u} a b))

/-- Relative structure-sheaf pushforward
`b_{QCoh,*} O_Z ⟶ f_{QCoh,*} O_{Y ×_X Z}` obtained from the right relative
pullback map and `structureSheafPullbackInv`. -/
def relativeStructurePushforward_right :
    (directImage b).obj (structureSheaf Z) ⟶
      (directImage (fibreProductHom a b)).obj
        (structureSheaf (TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b)) :=
  relativePullbackMap_right a b ≫
    (directImage (fibreProductHom a b)).map
      (structureSheafPullbackInv
        (TwoFibreProduct.snd.{u + 1, u, u + 1, u} a b))

/-- The canonical underived Künneth morphism
`a_{QCoh,*} O_Y ⊗_{O_X} b_{QCoh,*} O_Z ⟶ f_{QCoh,*} O_{Y ×_X Z}` of
quasi-coherent structure sheaves. -/
def kunnethMap :
    tensor ((directImage a).obj (structureSheaf Y))
      ((directImage b).obj (structureSheaf Z)) ⟶
      (directImage (fibreProductHom a b)).obj
        (structureSheaf (TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b)) :=
  tensorHom (relativeStructurePushforward a b)
      (relativeStructurePushforward_right a b) ≫
    directImage_tensorComparison (fibreProductHom a b)
        (toLQCohFbc_isRightAdjoint_toQCoh X).some
        (structureSheaf (TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b))
        (structureSheaf (TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b)) ≫
      (directImage (fibreProductHom a b)).map
        (structureSheafMul (TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b))

/-- `kunnethMap a b` is the tensor of the two relative structure-sheaf
pushforwards, followed by `directImage_tensorComparison` and multiplication of
`O_{Y ×_X Z}`. -/
theorem kunnethMap_spec :
    kunnethMap a b =
      tensorHom (relativeStructurePushforward a b)
          (relativeStructurePushforward_right a b) ≫
        directImage_tensorComparison (fibreProductHom a b)
            (toLQCohFbc_isRightAdjoint_toQCoh X).some
            (structureSheaf (TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b))
            (structureSheaf (TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b)) ≫
          (directImage (fibreProductHom a b)).map
            (structureSheafMul
              (TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b)) :=
  sorry

end QCoh

end AlgebraicGeometry.GroupoidsOver
