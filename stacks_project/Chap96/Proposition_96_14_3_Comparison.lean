/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.TwoCell
public import ReasLib.CategoryTheory.Fibered.Groupoids.UnderlyingFunctorIso
public import stacks_project.Chap78.Lemma_78_12_3_QCoh
public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap96.Lemma_96_11_2_Pullback
public import stacks_project.Chap96.Lemma_96_13_2
public import stacks_project.Chap96.Lemma_96_14_2
import Mathlib.Tactic.CrossRefAttribute

/-!
# Atlas 2-cell and equivariance for quotient-stack QCoh

The defining atlas square of `[U / R]` supplies a 2-cell `x ∘ s ⟶ x ∘ t`. After
restriction to the small étale site of `U`, this is the equivariance map
`α : t_small^* G ⟶ s_small^* G` of an object of `QCoh(U, R, s, t, c)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.GroupoidAlgebraicSpace
open CategoryTheory.ObjectProperty
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)

/-- Identity presentation of the algebraic space of objects as a category fibred in
groupoids. -/
def idSpace (X : AlgebraicSpace S) : X.toGroupoids ≌ X.toGroupoids :=
  Bicategory.Equivalence.id _

/-- The composite `π ∘ s : 𝒮_R ⟶ [U / R]`. -/
def atlasSource : G.R.left.toGroupoids ⟶ G.quotientStack :=
  AlgebraicSpace.toGroupoids.map G.s.left ≫ G.atlas

/-- `atlasSource` is `toGroupoids.map G.s.left` followed by the atlas. -/
theorem atlasSource_eq :
    atlasSource G = AlgebraicSpace.toGroupoids.map G.s.left ≫ G.atlas :=
  rfl

/-- The composite `π ∘ t : 𝒮_R ⟶ [U / R]`. -/
def atlasTarget : G.R.left.toGroupoids ⟶ G.quotientStack :=
  AlgebraicSpace.toGroupoids.map G.t.left ≫ G.atlas

/-- `atlasTarget` is `toGroupoids.map G.t.left` followed by the atlas. -/
theorem atlasTarget_eq :
    atlasTarget G = AlgebraicSpace.toGroupoids.map G.t.left ≫ G.atlas :=
  rfl

/-- The `R`-valued functor-of-points arrow carried by an object of `𝒮_R`. -/
def arrowPoint (x : G.R.left.toGroupoids.total) :
    G.R.left.functorOfPoints.obj x.unop.fst :=
  x.unop.snd

/-- The object inclusion of `𝒮_R` into `[U /ₚ R]` along `s`. -/
def atlasSourcePre : G.R.left.toGroupoids ⟶ G.preQuotient :=
  AlgebraicSpace.toGroupoids.map G.s.left ≫ G.atlasToPreQuotient

/-- `atlasSourcePre` is `toGroupoids.map G.s.left` followed by the object inclusion. -/
theorem atlasSourcePre_eq :
    atlasSourcePre G = AlgebraicSpace.toGroupoids.map G.s.left ≫ G.atlasToPreQuotient :=
  rfl

/-- The object inclusion of `𝒮_R` into `[U /ₚ R]` along `t`. -/
def atlasTargetPre : G.R.left.toGroupoids ⟶ G.preQuotient :=
  AlgebraicSpace.toGroupoids.map G.t.left ≫ G.atlasToPreQuotient

/-- `atlasTargetPre` is `toGroupoids.map G.t.left` followed by the object inclusion. -/
theorem atlasTargetPre_eq :
    atlasTargetPre G = AlgebraicSpace.toGroupoids.map G.t.left ≫ G.atlasToPreQuotient :=
  rfl

/-- The object of `[U /ₚ R]` obtained by applying the atlas-to-prequotient functor
after `s`. -/
def atlasSourcePreObj (x : G.R.left.toGroupoids.total) : G.preQuotient.total :=
  (toFunctor (atlasSourcePre G)).obj x

/-- `atlasSourcePreObj` is the total functor of `atlasSourcePre`. -/
theorem atlasSourcePreObj_eq (x : G.R.left.toGroupoids.total) :
    atlasSourcePreObj G x = (toFunctor (atlasSourcePre G)).obj x :=
  rfl

/-- The object of `[U /ₚ R]` obtained by applying the atlas-to-prequotient functor
after `t`. -/
def atlasTargetPreObj (x : G.R.left.toGroupoids.total) : G.preQuotient.total :=
  (toFunctor (atlasTargetPre G)).obj x

/-- `atlasTargetPreObj` is the total functor of `atlasTargetPre`. -/
theorem atlasTargetPreObj_eq (x : G.R.left.toGroupoids.total) :
    atlasTargetPreObj G x = (toFunctor (atlasTargetPre G)).obj x :=
  rfl

/-- The morphism of `[U /ₚ R]` over `id_T` whose fiber is the `R`-arrow of `x`. -/
def sourceTargetPreApp (x : G.R.left.toGroupoids.total) :
    atlasSourcePreObj G x ⟶ atlasTargetPreObj G x where
  base := 𝟙 _
  fiber := FunctorPointHom.ofArrow (arrowPoint G x) sorry sorry

/-- The canonical 2-cell `π_p ∘ s ⟶ π_p ∘ t` of the atlas square, before stackification. -/
def sourceTargetPre : atlasSourcePre G ⟶ atlasTargetPre G :=
  ofBasedNatTrans
    { toNatTrans :=
        { app := fun x => sourceTargetPreApp G x
          naturality := sorry }
      isHomLift' := sorry }

/-- The canonical 2-cell `x ∘ s ⟶ x ∘ t` of the atlas square, obtained by whiskering the
prestack cell by stackification. -/
def sourceTarget : atlasSource G ⟶ atlasTarget G :=
  sourceTargetPre G ▷ G.stackificationHom

/-- `sourceTarget` is the prestack cell whiskered by stackification. -/
theorem sourceTarget_eq :
    sourceTarget G = sourceTargetPre G ▷ G.stackificationHom :=
  rfl

/-- Algebraic-space morphism recovered from `toGroupoids.map f` along identity
presentations. -/
def recoveredIdMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) : X ⟶ Y :=
  recoveredHom (idSpace X) (idSpace Y) (AlgebraicSpace.toGroupoids.map f)

/-- Recovering `toGroupoids.map f` along identity presentations returns `f`. -/
theorem recoveredIdMap_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    recoveredIdMap f = f :=
  sorry

/-- The 2-iso required by `restrict_pullbackIso` for `toGroupoids.map f` and the
identity presentations, by unitors and the named recovery equality. -/
def recoveredIdMapTwoCell {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (AlgebraicSpace.toGroupoids.map f ≫ (idSpace Y).symm.hom) ≅
      ((idSpace X).symm.hom ≫
        AlgebraicSpace.toGroupoids.map (recoveredIdMap f)) :=
  ρ_ (AlgebraicSpace.toGroupoids.map f) ≪≫
    eqToIso
      (congrArg AlgebraicSpace.toGroupoids.map (recoveredIdMap_eq f)).symm ≪≫
      (λ_ (AlgebraicSpace.toGroupoids.map (recoveredIdMap f))).symm

/-- Restriction of the atlas pullback to the small étale site of `U`. -/
def atlasRestrict (F : QCoh G.quotientStack) : AlgebraicSpace.QCoh G.U.left :=
  (restrict (idSpace G.U.left)).obj ((pullback G.atlas).obj F)

/-- `atlasRestrict F` is restriction of `π^* F` along the identity presentation of `U`. -/
theorem atlasRestrict_eq (F : QCoh G.quotientStack) :
    atlasRestrict G F =
      (restrict (idSpace G.U.left)).obj ((pullback G.atlas).obj F) :=
  rfl

/-- Restriction after pullback along `toGroupoids.map G.s.left` compares with
small-étale pullback along `G.s.left`. -/
def restrict_atlasPullbackIso_source :
    pullback (AlgebraicSpace.toGroupoids.map G.s.left) ⋙ restrict (idSpace G.R.left) ≅
      restrict (idSpace G.U.left) ⋙ AlgebraicSpace.QCoh.pullback G.s.left :=
  restrict_pullbackIso (idSpace G.R.left) (idSpace G.U.left)
      (AlgebraicSpace.toGroupoids.map G.s.left) (recoveredIdMapTwoCell G.s.left) ≪≫
    Functor.isoWhiskerLeft (restrict (idSpace G.U.left))
      (GroupoidAlgebraicSpace.pullbackEqIso (recoveredIdMap_eq G.s.left))

/-- Restriction after pullback along `toGroupoids.map G.t.left` compares with
small-étale pullback along `G.t.left`. -/
def restrict_atlasPullbackIso_target :
    pullback (AlgebraicSpace.toGroupoids.map G.t.left) ⋙ restrict (idSpace G.R.left) ≅
      restrict (idSpace G.U.left) ⋙ AlgebraicSpace.QCoh.pullback G.t.left :=
  restrict_pullbackIso (idSpace G.R.left) (idSpace G.U.left)
      (AlgebraicSpace.toGroupoids.map G.t.left) (recoveredIdMapTwoCell G.t.left) ≪≫
    Functor.isoWhiskerLeft (restrict (idSpace G.U.left))
      (GroupoidAlgebraicSpace.pullbackEqIso (recoveredIdMap_eq G.t.left))

/-- The cartesian total functors of `f` and `g` compose to the cartesian total functor
of the composite, after identifying each with `toFunctor`. -/
def cartesianToFunctor_compIso {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (toCartesianBasedFunctor f).toFunctor ⋙ (toCartesianBasedFunctor g).toFunctor ≅
      (toCartesianBasedFunctor (f ≫ g)).toFunctor :=
  eqToIso
      (congrArg₂ (fun F G => F ⋙ G) (cartesian_toFunctor_eq f)
        (cartesian_toFunctor_eq g)) ≪≫
    FullSubbicategory.toFunctor.compIso f g ≪≫
      eqToIso (cartesian_toFunctor_eq (f ≫ g)).symm

/-- Composite of cartesian total functors is continuous for inherited fppf topologies. -/
instance cartesianToFunctor_comp_isContinuous {X Y Z : GroupoidsOver S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((toCartesianBasedFunctor f).toFunctor ⋙
        (toCartesianBasedFunctor g).toFunctor).IsContinuous
      (inheritedFppfTopology X) (inheritedFppfTopology Z) :=
  Functor.isContinuous_comp (toCartesianBasedFunctor f).toFunctor
    (toCartesianBasedFunctor g).toFunctor (inheritedFppfTopology X)
    (inheritedFppfTopology Y) (inheritedFppfTopology Z)

/-- The composite structure-sheaf map along cartesian total functors of `f` and `g`. -/
def structureSheafMap_compData {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    structureSheaf X ⟶
      (((toCartesianBasedFunctor f).toFunctor ⋙
          (toCartesianBasedFunctor g).toFunctor).sheafPushforwardContinuous RingCat.{u}
        (inheritedFppfTopology X) (inheritedFppfTopology Z)).obj (structureSheaf Z) :=
  structureSheafMap f ≫
    ((toCartesianBasedFunctor f).toFunctor.sheafPushforwardContinuous RingCat.{u}
        (inheritedFppfTopology X) (inheritedFppfTopology Y)).map (structureSheafMap g)

/-- Module inverse image along a composite, before transporting the total functor. -/
def modulePullback_comp₀ {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullback g ⋙ modulePullback f ≅
      SheafOfModules.pushforward (structureSheafMap_compData f g) :=
  SheafOfModules.pushforwardComp (structureSheafMap f) (structureSheafMap g)

/-- Transport of composite inverse image along the cartesian total-functor composition
isomorphism. -/
def modulePullback_comp₁ {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    SheafOfModules.pushforward (structureSheafMap_compData f g) ≅
      SheafOfModules.pushforward
        (structureSheafMap_compData f g ≫
          (Functor.sheafPushforwardContinuousNatTrans
              (cartesianToFunctor_compIso f g).hom RingCat.{u}
              (inheritedFppfTopology X) (inheritedFppfTopology Z)).app
            (structureSheaf Z)) :=
  SheafOfModules.pushforwardNatIso (structureSheafMap_compData f g)
    (cartesianToFunctor_compIso f g)

/-- The transported composite structure-sheaf map agrees with the structure-sheaf map
of the composite 1-morphism. -/
theorem structureSheafMap_comp {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    structureSheafMap_compData f g ≫
        (Functor.sheafPushforwardContinuousNatTrans
            (cartesianToFunctor_compIso f g).hom RingCat.{u}
            (inheritedFppfTopology X) (inheritedFppfTopology Z)).app
          (structureSheaf Z) =
      structureSheafMap (f ≫ g) :=
  sorry

/-- Align the transported composite inverse image with inverse image along the composite. -/
def modulePullback_comp₂ {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    SheafOfModules.pushforward
        (structureSheafMap_compData f g ≫
          (Functor.sheafPushforwardContinuousNatTrans
              (cartesianToFunctor_compIso f g).hom RingCat.{u}
              (inheritedFppfTopology X) (inheritedFppfTopology Z)).app
            (structureSheaf Z)) ≅
      modulePullback (f ≫ g) :=
  SheafOfModules.pushforwardCongr (structureSheafMap_comp f g)

/-- Inverse image of modules along a composite 1-morphism is the composite of the
inverse images. -/
def modulePullback_comp {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullback g ⋙ modulePullback f ≅ modulePullback (f ≫ g) :=
  modulePullback_comp₀ f g ≪≫ modulePullback_comp₁ f g ≪≫ modulePullback_comp₂ f g

/-- The cartesian total functor of `h₂` transported along `toFunctorIso e` agrees with
the cartesian total functor of `h₁`. -/
def cartesianToFunctorIso {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (e : h₁ ≅ h₂) :
    (toCartesianBasedFunctor h₁).toFunctor ≅ (toCartesianBasedFunctor h₂).toFunctor :=
  eqToIso (cartesian_toFunctor_eq h₁) ≪≫ toFunctorIso e ≪≫
    (eqToIso (cartesian_toFunctor_eq h₂)).symm

/-- Transport of inverse image along the real total-functor isomorphism. -/
def modulePullback_iso₀ {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (e : h₁ ≅ h₂) :
    modulePullback h₂ ≅
      SheafOfModules.pushforward
        (structureSheafMap h₂ ≫
          (Functor.sheafPushforwardContinuousNatTrans (cartesianToFunctorIso e).hom
              RingCat.{u} (inheritedFppfTopology X) (inheritedFppfTopology Y)).app
            (structureSheaf Y)) :=
  SheafOfModules.pushforwardNatIso (structureSheafMap h₂) (cartesianToFunctorIso e)

/-- The structure-sheaf map of `h₂` transported along `cartesianToFunctorIso e` agrees
with the structure-sheaf map of `h₁`. -/
theorem structureSheafMap_iso {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (e : h₁ ≅ h₂) :
    structureSheafMap h₂ ≫
        (Functor.sheafPushforwardContinuousNatTrans (cartesianToFunctorIso e).hom
            RingCat.{u} (inheritedFppfTopology X) (inheritedFppfTopology Y)).app
          (structureSheaf Y) =
      structureSheafMap h₁ :=
  sorry

/-- Align the transported inverse image with inverse image along `h₁`. -/
def modulePullback_iso₁ {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (e : h₁ ≅ h₂) :
    SheafOfModules.pushforward
        (structureSheafMap h₂ ≫
          (Functor.sheafPushforwardContinuousNatTrans (cartesianToFunctorIso e).hom
              RingCat.{u} (inheritedFppfTopology X) (inheritedFppfTopology Y)).app
            (structureSheaf Y)) ≅
      modulePullback h₁ :=
  SheafOfModules.pushforwardCongr (structureSheafMap_iso e)

/-- A 2-isomorphism of 1-morphisms induces an isomorphism of module inverse images. -/
def modulePullbackIso {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (e : h₁ ≅ h₂) :
    modulePullback h₁ ≅ modulePullback h₂ :=
  (modulePullback_iso₀ e ≪≫ modulePullback_iso₁ e).symm

/-- Restriction of a 2-isomorphism of 1-morphisms to quasi-coherent pullbacks. -/
def pullbackIso {X Y : GroupoidsOver S} {f g : X ⟶ Y} (e : f ≅ g) :
    pullback g ≅ pullback f :=
  NatIso.ofComponents
    (fun F =>
      (quasiCoherentModuleProperty X).isoMk
        ((FullSubcategory.restrict.compιIso (modulePullback g)
            (modulePullback_le_inverseImage g)).app F ≪≫
          ((modulePullbackIso e).app F.obj).symm ≪≫
            (FullSubcategory.restrict.compιIso (modulePullback f)
                (modulePullback_le_inverseImage f)).symm.app F))
    sorry

/-- Composition of quasi-coherent pullbacks along a composite 1-morphism. -/
def pullback_comp {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  NatIso.ofComponents
    (fun F =>
      (quasiCoherentModuleProperty X).isoMk
        ((FullSubcategory.restrict.compιIso (modulePullback (f ≫ g))
            (modulePullback_le_inverseImage (f ≫ g))).app F ≪≫
          ((modulePullback_comp f g).app F.obj).symm ≪≫
            (modulePullback f).mapIso
              ((FullSubcategory.restrict.compιIso (modulePullback g)
                  (modulePullback_le_inverseImage g)).symm.app F) ≪≫
              (FullSubcategory.restrict.compιIso (modulePullback f)
                  (modulePullback_le_inverseImage f)).symm.app
                ((pullback g).obj F)))
    sorry

/-- The total-functor transformation of a `2`-cell, after identifying cartesian
total functors with `toFunctor`. -/
def cartesianToFunctorHom {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (α : h₁ ⟶ h₂) :
    (toCartesianBasedFunctor h₁).toFunctor ⟶ (toCartesianBasedFunctor h₂).toFunctor :=
  eqToHom (cartesian_toFunctor_eq h₁) ≫ toNatTrans α ≫
    eqToHom (cartesian_toFunctor_eq h₂).symm

/-- `cartesianToFunctorHom` is `toNatTrans` after cartesian-to-`toFunctor`
identifications. -/
theorem cartesianToFunctorHom_eq {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y}
    (α : h₁ ⟶ h₂) :
    cartesianToFunctorHom α =
      eqToHom (cartesian_toFunctor_eq h₁) ≫ toNatTrans α ≫
        eqToHom (cartesian_toFunctor_eq h₂).symm :=
  rfl

/-- Contravariant transport of inverse image along the total-functor map of a
`2`-cell. -/
def modulePullback_hom₀ {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (α : h₁ ⟶ h₂) :
    modulePullback h₂ ⟶
      SheafOfModules.pushforward
        (structureSheafMap h₂ ≫
          (Functor.sheafPushforwardContinuousNatTrans (cartesianToFunctorHom α)
              RingCat.{u} (inheritedFppfTopology X) (inheritedFppfTopology Y)).app
            (structureSheaf Y)) :=
  SheafOfModules.pushforwardNatTrans (structureSheafMap h₂) (cartesianToFunctorHom α)

/-- The structure-sheaf map of `h₂` transported along `cartesianToFunctorHom α`
agrees with the structure-sheaf map of `h₁`. -/
theorem structureSheafMap_hom {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (α : h₁ ⟶ h₂) :
    structureSheafMap h₂ ≫
        (Functor.sheafPushforwardContinuousNatTrans (cartesianToFunctorHom α)
            RingCat.{u} (inheritedFppfTopology X) (inheritedFppfTopology Y)).app
          (structureSheaf Y) =
      structureSheafMap h₁ :=
  sorry

/-- Align the transported inverse image with inverse image along `h₁`. -/
def modulePullback_hom₁ {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (α : h₁ ⟶ h₂) :
    SheafOfModules.pushforward
        (structureSheafMap h₂ ≫
          (Functor.sheafPushforwardContinuousNatTrans (cartesianToFunctorHom α)
              RingCat.{u} (inheritedFppfTopology X) (inheritedFppfTopology Y)).app
            (structureSheaf Y)) ⟶
      modulePullback h₁ :=
  (SheafOfModules.pushforwardCongr (structureSheafMap_hom α)).hom

/-- A `2`-cell of 1-morphisms induces a morphism of module inverse images, without
inverting the cell. -/
def modulePullbackHom {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (α : h₁ ⟶ h₂) :
    modulePullback h₂ ⟶ modulePullback h₁ :=
  modulePullback_hom₀ α ≫ modulePullback_hom₁ α

/-- `modulePullbackHom` is the contravariant pushforward map of the `2`-cell. -/
theorem modulePullbackHom_eq {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (α : h₁ ⟶ h₂) :
    modulePullbackHom α = modulePullback_hom₀ α ≫ modulePullback_hom₁ α :=
  rfl

/-- Restriction of a `2`-cell of 1-morphisms to quasi-coherent pullbacks. -/
def pullbackMap {X Y : GroupoidsOver S} {f g : X ⟶ Y} (α : f ⟶ g) :
    pullback g ⟶ pullback f where
  app F :=
    (quasiCoherentModuleProperty X).homMk
      ((FullSubcategory.restrict.compιIso (modulePullback g)
          (modulePullback_le_inverseImage g)).hom.app F ≫
        (modulePullbackHom α).app F.obj ≫
          (FullSubcategory.restrict.compιIso (modulePullback f)
              (modulePullback_le_inverseImage f)).inv.app F)
  naturality := sorry

/-- The atlas 2-cell as a morphism of pullbacks to `𝒮_R`, the contravariant
image of `sourceTarget : atlasSource ⟶ atlasTarget`. -/
def atlasActionAux (F : QCoh G.quotientStack) :
    (pullback (AlgebraicSpace.toGroupoids.map G.t.left)).obj ((pullback G.atlas).obj F) ⟶
      (pullback (AlgebraicSpace.toGroupoids.map G.s.left)).obj ((pullback G.atlas).obj F) :=
  (pullback_comp (AlgebraicSpace.toGroupoids.map G.t.left) G.atlas).inv.app F ≫
    (pullbackMap (sourceTarget G)).app F ≫
      (pullback_comp (AlgebraicSpace.toGroupoids.map G.s.left) G.atlas).hom.app F

/-- The equivariance map `α : t_small^* G ⟶ s_small^* G` of `atlasRestrict F`. -/
def action (F : QCoh G.quotientStack) :
    (AlgebraicSpace.QCoh.pullback G.t.left).obj (atlasRestrict G F) ⟶
      (AlgebraicSpace.QCoh.pullback G.s.left).obj (atlasRestrict G F) :=
  (restrict_atlasPullbackIso_target G).inv.app ((pullback G.atlas).obj F) ≫
    (restrict (idSpace G.R.left)).map (atlasActionAux G F) ≫
      (restrict_atlasPullbackIso_source G).hom.app ((pullback G.atlas).obj F)

/-- `action F` is the transport of `atlasActionAux` through the source and target
restriction comparisons. -/
theorem action_spec (F : QCoh G.quotientStack) :
    action G F =
      (restrict_atlasPullbackIso_target G).inv.app ((pullback G.atlas).obj F) ≫
        (restrict (idSpace G.R.left)).map (atlasActionAux G F) ≫
          (restrict_atlasPullbackIso_source G).hom.app ((pullback G.atlas).obj F) :=
  rfl

/-- The atlas equivariance map `α` is an isomorphism. -/
instance action_isIso (F : QCoh G.quotientStack) : IsIso (action G F) :=
  sorry

/-- The atlas equivariance map satisfies the cocycle condition on
`R ×_{s,U,t} R`. -/
theorem action_cocycle (F : QCoh G.quotientStack) :
    GroupoidAlgebraicSpace.Cocycle G (atlasRestrict G F) (action G F) :=
  sorry

/-- The atlas equivariance map satisfies the unit condition along the identity
section of the groupoid. -/
theorem action_unit (F : QCoh G.quotientStack) :
    GroupoidAlgebraicSpace.Unit G (atlasRestrict G F) (action G F) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.QCoh
