/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Sites.Point.Map
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import stacks_project.Chap66.Lemma_66_18_3
public import stacks_project.Chap66.Lemma_66_18_8_Pullback
public import stacks_project.Chap66.Lemma_66_18_12_Restriction
public import stacks_project.Chap66.Lemma_66_19_9_Stalk
public import stacks_project.Chap66.Lemma_66_27_1_Hom
public import stacks_project.Chap67.Definition_67_13_2_InverseImage
public import stacks_project.Chap67.Lemma_67_13_5_Complement
public import stacks_project.Chap69.Lemma_69_6_5_Sections
public import stacks_project.Chap81.Lemma_81_10_1_Stalk

/-!
# Comparison of two-term étale stalk complexes

A morphism of algebraic spaces induces a canonical comparison from the stalk of a
pushforward at the image geometric point to the stalk at the source. Applied to the
adjunction unit of restriction to the open complement of an inverse image, this yields
the map of two-term complexes used in Lemma 81.10.2.

The inverse-image stalk identification transports
`sheafFiberComapIso` along the Kan-extension adjunction used by `sheafInverseImage`,
then compares the resulting comap fibre with the small étale stalk at `ȳ.map f` by the
`Over.mapPullbackAdj` fibre maps of `smallEtaleInverseImage_comapFiberHom` /
`smallEtaleInverseImage_comapFiberInv`. Only `hom_inv_id`, naturality, and `Arrow.w`
are deferred.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.GrothendieckTopology.Point
open CategoryTheory.Functor
open CategoryTheory.Functor.sheafPullbackConstruction

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The open complement immersion `j' : Y \ f⁻¹Z ⟶ Y`. -/
abbrev complementOpenImmersion {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] :
    closedImmersionComplement (inverseImageι f i) ⟶ Y :=
  closedImmersionComplementι (inverseImageι f i)

/-- The adjunction unit `G ⟶ j'_*(j'⁻¹ G)` of restriction to the open complement of
`f⁻¹Z`. -/
def restrictUnit {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (G : EtaleSheaf Y) :
    G ⟶
      (sheafPushforward AddCommGrpCat.{u + 1} (complementOpenImmersion f i)).obj
        ((sheafInverseImage AddCommGrpCat.{u + 1} (complementOpenImmersion f i)).obj G) :=
  (sheafInverseImageAdjunction (complementOpenImmersion f i)).unit.app G

/-- `restrictUnit` is the unit of `sheafInverseImageAdjunction` at `G`. -/
theorem restrictUnit_eq {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (G : EtaleSheaf Y) :
    restrictUnit f i G =
      (sheafInverseImageAdjunction (complementOpenImmersion f i)).unit.app G :=
  rfl

/-- Recover a morphism of schemes over `S` from a morphism of the associated algebraic
spaces, via the Yoneda embedding. -/
def schemeHomOfAlgebraicSpace {U V : Over S} (φ : ofOver U ⟶ ofOver V) : U ⟶ V :=
  Yoneda.fullyFaithful.preimage (φ : yoneda.obj U ⟶ yoneda.obj V)

/-- Convert a small-étale lift of `x̄` through `U` to a spaces-étale lift through the
image of `U` under `smallEtaleInclusion`. -/
def smallLift_to_spacesLift {X : AlgebraicSpace S} (xbar : GeometricPoint X)
    {U : smallEtaleSite X}
    (α : (GeometricPoint.toSmallEtalePoint xbar).fiber.obj U) :
    (GeometricPoint.toSpacesEtalePoint xbar).fiber.obj ((smallEtaleInclusion X).obj U) :=
  CategoryTheory.Over.homMk (ofOverMap α.left) sorry

/-- Convert a spaces-étale lift of `x̄` through `inclusion U` back to a small-étale lift
through `U`. -/
def spacesLift_to_smallLift {X : AlgebraicSpace S} (xbar : GeometricPoint X)
    {U : smallEtaleSite X}
    (β : (GeometricPoint.toSpacesEtalePoint xbar).fiber.obj ((smallEtaleInclusion X).obj U)) :
    (GeometricPoint.toSmallEtalePoint xbar).fiber.obj U :=
  CategoryTheory.CostructuredArrow.homMk (schemeHomOfAlgebraicSpace β.left) sorry

/-- Étale base change is a morphism of sites from the small étale site of `X` to the
spaces étale site of `Y`. -/
instance etaleBaseChange_isMorphismOfSites {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    IsMorphismOfSites (smallEtaleTopology X) (spacesEtaleTopology Y) (etaleBaseChange f) :=
  sorry

/-- The category of spaces-étale lifts of `ȳ` along `etaleBaseChange f` is initially small. -/
instance instInitiallySmall_etaleBaseChange_spacesFiber {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) (ybar : GeometricPoint Y) :
    InitiallySmall
      ((etaleBaseChange f ⋙ (GeometricPoint.toSpacesEtalePoint ybar).fiber).Elements) :=
  sorry

/-- The category of spaces-étale lifts of `ȳ` along `spacesEtalePullback f` is initially small. -/
instance instInitiallySmall_spacesEtalePullback_fiber {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) (ybar : GeometricPoint Y) :
    InitiallySmall
      ((spacesEtalePullback f ⋙ (GeometricPoint.toSpacesEtalePoint ybar).fiber).Elements) :=
  sorry

/-- Restriction of a spaces-étale sheaf to the small étale site, as abelian sheaves. -/
abbrev smallRestriction {X : AlgebraicSpace S} :
    Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1} ⥤ EtaleSheaf X :=
  (smallEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (smallEtaleTopology X) (spacesEtaleTopology X)

/-- Kan-extension construction of inverse image along `etaleBaseChange f`, before restriction
to the small étale site of `Y`. -/
abbrev inverseImageLan {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    EtaleSheaf X ⥤ Sheaf (spacesEtaleTopology Y) AddCommGrpCat.{u + 1} :=
  sheafPullbackConstruction.sheafPullback (etaleBaseChange f) AddCommGrpCat.{u + 1}
    (smallEtaleTopology X) (spacesEtaleTopology Y)

/-- The Kan-extension adjunction presenting inverse image along `etaleBaseChange f`. -/
def inverseImageLanAdjunction {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    inverseImageLan f ⊣
      (etaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (smallEtaleTopology X) (spacesEtaleTopology Y) :=
  sheafPullbackConstruction.sheafAdjunctionContinuous (etaleBaseChange f)
    AddCommGrpCat.{u + 1} (smallEtaleTopology X) (spacesEtaleTopology Y)

/-- The comap of the spaces-étale point of `ȳ` along `etaleBaseChange f`. -/
abbrev comappedSpacesPoint {X Y : AlgebraicSpace S} (f : Y ⟶ X) (ybar : GeometricPoint Y) :
    (smallEtaleTopology X).Point.{u + 1} :=
  (GeometricPoint.toSpacesEtalePoint ybar).comapOfMorphismOfSites (J := smallEtaleTopology X)
    (etaleBaseChange f)

/-- Identify the sheaf fibre of `comappedSpacesPoint` with the spaces-étale fibre of the
Kan-extension pullback, by conjugating the identity of skyscraper sheaves along
`inverseImageLanAdjunction`. -/
def spacesLanStalkIso {X Y : AlgebraicSpace S} (f : Y ⟶ X) (ybar : GeometricPoint Y) :
    (comappedSpacesPoint f ybar).sheafFiber ≅
      inverseImageLan f ⋙ (GeometricPoint.toSpacesEtalePoint ybar).sheafFiber :=
  (conjugateIsoEquiv
      ((inverseImageLanAdjunction f).comp
        (GeometricPoint.toSpacesEtalePoint ybar).skyscraperSheafAdjunction)
      (comappedSpacesPoint f ybar).skyscraperSheafAdjunction).symm
    ((GeometricPoint.toSpacesEtalePoint ybar).skyscraperSheafFunctorCompSheafPushforwardContinuous
      (etaleBaseChange f)
      (CoverPreserving.of_isContinuous (etaleBaseChange f) (smallEtaleTopology X)
        (spacesEtaleTopology Y))
      AddCommGrpCat.{u + 1})

/-- `spacesLanStalkIso` is the conjugate of the identity comparison of skyscraper sheaves. -/
theorem spacesLanStalkIso_eq {X Y : AlgebraicSpace S} (f : Y ⟶ X) (ybar : GeometricPoint Y) :
    spacesLanStalkIso f ybar =
      (conjugateIsoEquiv
          ((inverseImageLanAdjunction f).comp
            (GeometricPoint.toSpacesEtalePoint ybar).skyscraperSheafAdjunction)
          (comappedSpacesPoint f ybar).skyscraperSheafAdjunction).symm
        ((GeometricPoint.toSpacesEtalePoint ybar).skyscraperSheafFunctorCompSheafPushforwardContinuous
          (etaleBaseChange f)
          (CoverPreserving.of_isContinuous (etaleBaseChange f) (smallEtaleTopology X)
            (spacesEtaleTopology Y))
          AddCommGrpCat.{u + 1}) :=
  rfl

/-- Transport a spaces-étale fibre element along
`smallEtaleInclusion_comp_spacesEtalePullback`. -/
def spacesFiber_baseChangeIso {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (ybar : GeometricPoint Y) (V : smallEtaleSite X) :
    (GeometricPoint.toSpacesEtalePoint ybar).fiber.obj
        ((spacesEtalePullback f).obj ((smallEtaleInclusion X).obj V)) ⟶
      (GeometricPoint.toSpacesEtalePoint ybar).fiber.obj ((etaleBaseChange f).obj V) :=
  (GeometricPoint.toSpacesEtalePoint ybar).fiber.map
    ((smallEtaleInclusion_comp_spacesEtalePullback f).hom.app V)

/-- Reverse transport of a spaces-étale fibre element along
`smallEtaleInclusion_comp_spacesEtalePullback`. -/
def spacesFiber_baseChangeIso_symm {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (ybar : GeometricPoint Y) (V : smallEtaleSite X) :
    (GeometricPoint.toSpacesEtalePoint ybar).fiber.obj ((etaleBaseChange f).obj V) ⟶
      (GeometricPoint.toSpacesEtalePoint ybar).fiber.obj
        ((spacesEtalePullback f).obj ((smallEtaleInclusion X).obj V)) :=
  (GeometricPoint.toSpacesEtalePoint ybar).fiber.map
    ((smallEtaleInclusion_comp_spacesEtalePullback f).inv.app V)

/-- Send a small-étale lift of `x̄ = ȳ.map f` through `V` to a spaces-étale lift of `ȳ`
through `Y ×_X V`. -/
def imageFiberToSpacesBaseChangeFiber {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (ybar : GeometricPoint Y) {V : smallEtaleSite X}
    (α : (GeometricPoint.toSmallEtalePoint (ybar.map f)).fiber.obj V) :
    (GeometricPoint.toSpacesEtalePoint ybar).fiber.obj ((etaleBaseChange f).obj V) :=
  spacesFiber_baseChangeIso f ybar V
    ((smallEtaleInverseImage_comapFiberInv (X := Y) (Y := X) f ybar).app
      ((smallEtaleInclusion X).obj V)
      (smallLift_to_spacesLift (ybar.map f) α))

/-- Send a spaces-étale lift of `ȳ` through `Y ×_X V` to a small-étale lift of
`x̄ = ȳ.map f` through `V`. -/
def spacesBaseChangeFiberToImageFiber {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (ybar : GeometricPoint Y) {V : smallEtaleSite X}
    (β : (GeometricPoint.toSpacesEtalePoint ybar).fiber.obj ((etaleBaseChange f).obj V)) :
    (GeometricPoint.toSmallEtalePoint (ybar.map f)).fiber.obj V :=
  spacesLift_to_smallLift (ybar.map f)
    ((smallEtaleInverseImage_comapFiberHom (X := Y) (Y := X) f ybar).app
      ((smallEtaleInclusion X).obj V)
      (spacesFiber_baseChangeIso_symm f ybar V β))

/-- Compare the small étale stalk at `ȳ.map f` with the comap fibre of the spaces-étale
point of `ȳ` along `etaleBaseChange f`. -/
def comapImageStalkIso {X Y : AlgebraicSpace S} (f : Y ⟶ X) (ybar : GeometricPoint Y)
    (H : EtaleSheaf X) :
    (etaleAbelianStalk (ybar.map f)).obj H ≅
      (comappedSpacesPoint f ybar).sheafFiber.obj H where
  hom :=
    (GeometricPoint.toSmallEtalePoint (ybar.map f)).presheafFiberDesc
      (fun V α ↦
        (comappedSpacesPoint f ybar).toPresheafFiber V
          (imageFiberToSpacesBaseChangeFiber f ybar α) H.obj)
      sorry
  inv :=
    (comappedSpacesPoint f ybar).presheafFiberDesc
      (fun V β ↦
        (GeometricPoint.toSmallEtalePoint (ybar.map f)).toPresheafFiber V
          (spacesBaseChangeFiberToImageFiber f ybar β) H.obj)
      sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Forward map of `comapImageStalkIso`. -/
theorem comapImageStalkIso_hom {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (ybar : GeometricPoint Y) (H : EtaleSheaf X) :
    (comapImageStalkIso f ybar H).hom =
      (GeometricPoint.toSmallEtalePoint (ybar.map f)).presheafFiberDesc
        (fun V α ↦
          (comappedSpacesPoint f ybar).toPresheafFiber V
            (imageFiberToSpacesBaseChangeFiber f ybar α) H.obj)
        sorry :=
  rfl

/-- The chosen étale atlas of an algebraic space is surjective on maps out of the
source of a geometric point, since that source is the spectrum of an algebraically
closed field. -/
theorem atlas_app_surjective_geometricPoint {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) (Y : AlgebraicSpace S) :
    Function.Surjective (Y.atlas.choose_spec.choose.app (op xbar.overObj)) :=
  sorry

/-- The morphism in `Over S` obtained by lifting a spaces-étale neighborhood of `x̄`
through a chosen étale atlas chart of its target. -/
def spacesLift_atlasHom {X : AlgebraicSpace S} (xbar : GeometricPoint X)
    {W : spacesEtaleSite X}
    (β : (GeometricPoint.toSpacesEtalePoint xbar).fiber.obj W) :
    xbar.overObj ⟶ W.left.atlas.choose :=
  Function.surjInv (atlas_app_surjective_geometricPoint xbar W.left)
    (yonedaEquiv β.left)

/-- `spacesLift_atlasHom` is a section of the chosen atlas map of `W.left` over the
source of `x̄`. -/
theorem spacesLift_atlasHom_spec {X : AlgebraicSpace S} (xbar : GeometricPoint X)
    {W : spacesEtaleSite X}
    (β : (GeometricPoint.toSpacesEtalePoint xbar).fiber.obj W) :
    W.left.atlas.choose_spec.choose.app (op xbar.overObj)
        (spacesLift_atlasHom xbar β) =
      yonedaEquiv β.left :=
  sorry

/-- Convert a spaces-étale lift of `x̄` through `W` to a spaces-étale lift through the
chosen étale atlas chart of `W`, viewed in the small étale site of `X`. -/
def spacesLift_to_atlasSpacesLift {X : AlgebraicSpace S} (xbar : GeometricPoint X)
    {W : spacesEtaleSite X}
    (β : (GeometricPoint.toSpacesEtalePoint xbar).fiber.obj W)
    (φ : ofOver W.left.atlas.choose ⟶ X) [Etale φ] :
    (GeometricPoint.toSpacesEtalePoint xbar).fiber.obj
      ((smallEtaleInclusion X).obj (smallEtaleSite.mk φ)) :=
  CategoryTheory.Over.homMk (ofOverMap (spacesLift_atlasHom xbar β)) sorry

/-- Compare the small restriction stalk of a spaces-étale sheaf with the spaces-étale
sheaf fibre. -/
def restrictionStalkIso {X : AlgebraicSpace S} (xbar : GeometricPoint X)
    (G : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (etaleAbelianStalk xbar).obj (smallRestriction.obj G) ≅
      (GeometricPoint.toSpacesEtalePoint xbar).sheafFiber.obj G where
  hom :=
    (GeometricPoint.toSmallEtalePoint xbar).presheafFiberDesc
      (fun U α ↦
        (GeometricPoint.toSpacesEtalePoint xbar).toPresheafFiber
          ((smallEtaleInclusion X).obj U) (smallLift_to_spacesLift xbar α) G.obj)
      sorry
  inv :=
    (GeometricPoint.toSpacesEtalePoint xbar).presheafFiberDesc
      (fun W β ↦
        let U := W.left.atlas.choose
        let p := W.left.atlas.choose_spec.choose
        let ψ : ofOver U ⟶ W.left := homOfYonedaSection (yonedaEquiv p)
        let φ : ofOver U ⟶ X := ψ ≫ W.hom
        have : Etale φ := sorry
        let Us := smallEtaleSite.mk φ
        let ιUW : (smallEtaleInclusion X).obj Us ⟶ W :=
          MorphismProperty.Over.homMk ψ sorry
        G.obj.map ιUW.op ≫
          (GeometricPoint.toSmallEtalePoint xbar).toPresheafFiber Us
            (spacesLift_to_smallLift xbar (spacesLift_to_atlasSpacesLift xbar β φ))
            (smallRestriction.obj G).obj)
      sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Canonical identification `(f⁻¹ H)_ȳ ≅ H_{ȳ.map f}` of abelian étale stalks. -/
def inverseImageStalkIso {X Y : AlgebraicSpace S} (f : Y ⟶ X) (ybar : GeometricPoint Y) :
    sheafInverseImage AddCommGrpCat.{u + 1} f ⋙ etaleAbelianStalk ybar ≅
      etaleAbelianStalk (ybar.map f) :=
  NatIso.ofComponents
    (fun H ↦
      (restrictionStalkIso ybar ((inverseImageLan f).obj H) ≪≫
        (spacesLanStalkIso f ybar).symm.app H ≪≫
        (comapImageStalkIso f ybar H).symm))
    sorry

/-- Forward map of `inverseImageStalkIso` at `H`. -/
def inverseImageStalkHom_app {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (ybar : GeometricPoint Y) (H : EtaleSheaf X) :
    (etaleAbelianStalk ybar).obj ((sheafInverseImage AddCommGrpCat.{u + 1} f).obj H) ⟶
      (etaleAbelianStalk (ybar.map f)).obj H :=
  (inverseImageStalkIso f ybar).hom.app H

/-- Reverse map of `inverseImageStalkIso` at `H`. -/
def inverseImageStalkInv_app {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (ybar : GeometricPoint Y) (H : EtaleSheaf X) :
    (etaleAbelianStalk (ybar.map f)).obj H ⟶
      (etaleAbelianStalk ybar).obj ((sheafInverseImage AddCommGrpCat.{u + 1} f).obj H) :=
  (inverseImageStalkIso f ybar).inv.app H

/-- Canonical comparison `(f_* G)_{ȳ.map f} ⟶ G_ȳ`, obtained by transporting the
adjunction counit along `inverseImageStalkIso`. -/
def pushforwardStalkNatTrans {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (ybar : GeometricPoint Y) :
    sheafPushforward AddCommGrpCat.{u + 1} f ⋙ etaleAbelianStalk (ybar.map f) ⟶
      etaleAbelianStalk ybar where
  app G :=
    (inverseImageStalkIso f ybar).inv.app ((sheafPushforward AddCommGrpCat.{u + 1} f).obj G) ≫
      (etaleAbelianStalk ybar).map ((sheafInverseImageAdjunction f).counit.app G)
  naturality := sorry

/-- The component of `pushforwardStalkNatTrans` at `G` is the counit of inverse image
transported along `inverseImageStalkIso`. -/
theorem pushforwardStalkNatTrans_app {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (ybar : GeometricPoint Y) (G : EtaleSheaf Y) :
    (pushforwardStalkNatTrans f ybar).app G =
      (inverseImageStalkIso f ybar).inv.app ((sheafPushforward AddCommGrpCat.{u + 1} f).obj G) ≫
        (etaleAbelianStalk ybar).map ((sheafInverseImageAdjunction f).counit.app G) :=
  rfl

/-- The source two-term complex
`(f_* G)_{ȳ.map f} ⟶ (f_* j'_*(j'⁻¹ G))_{ȳ.map f}`. -/
def sourceTwoTerm {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (ybar : GeometricPoint Y) (G : EtaleSheaf Y) :
    (etaleAbelianStalk (ybar.map f)).obj
        ((sheafPushforward AddCommGrpCat.{u + 1} f).obj G) ⟶
      (etaleAbelianStalk (ybar.map f)).obj
        ((sheafPushforward AddCommGrpCat.{u + 1} f).obj
          ((sheafPushforward AddCommGrpCat.{u + 1} (complementOpenImmersion f i)).obj
            ((sheafInverseImage AddCommGrpCat.{u + 1} (complementOpenImmersion f i)).obj G))) :=
  (etaleAbelianStalk (ybar.map f)).map
    ((sheafPushforward AddCommGrpCat.{u + 1} f).map (restrictUnit f i G))

/-- `sourceTwoTerm` is the stalk at `ȳ.map f` of `f_*` applied to `restrictUnit`. -/
theorem sourceTwoTerm_eq {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (ybar : GeometricPoint Y) (G : EtaleSheaf Y) :
    sourceTwoTerm f i ybar G =
      (etaleAbelianStalk (ybar.map f)).map
        ((sheafPushforward AddCommGrpCat.{u + 1} f).map (restrictUnit f i G)) :=
  rfl

/-- The target two-term complex `G_ȳ ⟶ (j'_*(j'⁻¹ G))_ȳ`. -/
def targetTwoTerm {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (ybar : GeometricPoint Y) (G : EtaleSheaf Y) :
    (etaleAbelianStalk ybar).obj G ⟶
      (etaleAbelianStalk ybar).obj
        ((sheafPushforward AddCommGrpCat.{u + 1} (complementOpenImmersion f i)).obj
          ((sheafInverseImage AddCommGrpCat.{u + 1} (complementOpenImmersion f i)).obj G)) :=
  (etaleAbelianStalk ybar).map (restrictUnit f i G)

/-- `targetTwoTerm` is the stalk at `ȳ` of `restrictUnit`. -/
theorem targetTwoTerm_eq {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (ybar : GeometricPoint Y) (G : EtaleSheaf Y) :
    targetTwoTerm f i ybar G = (etaleAbelianStalk ybar).map (restrictUnit f i G) :=
  rfl

/-- The canonical map of two-term complexes of abelian groups comparing pushforward
stalks at `ȳ.map f` with stalks at `ȳ`. -/
def twoTermStalkComparison {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (ybar : GeometricPoint Y) (G : EtaleSheaf Y) :
    Arrow.mk (sourceTwoTerm f i ybar G) ⟶ Arrow.mk (targetTwoTerm f i ybar G) :=
  Arrow.homMk ((pushforwardStalkNatTrans f ybar).app G)
    ((pushforwardStalkNatTrans f ybar).app
      ((sheafPushforward AddCommGrpCat.{u + 1} (complementOpenImmersion f i)).obj
        ((sheafInverseImage AddCommGrpCat.{u + 1} (complementOpenImmersion f i)).obj G)))
    sorry

/-- The two-term comparison is a commutative square. -/
theorem twoTermStalkComparison_w {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (ybar : GeometricPoint Y) (G : EtaleSheaf Y) :
    (twoTermStalkComparison f i ybar G).left ≫ targetTwoTerm f i ybar G =
      sourceTwoTerm f i ybar G ≫ (twoTermStalkComparison f i ybar G).right :=
  Arrow.w (twoTermStalkComparison f i ybar G)

/-- Restriction along the étale open complement agrees with inverse image, as abelian
étale sheaves. -/
def inverseImageIsoRestriction {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] :
    etaleRestrictionSheaf (complementOpenImmersion f i) AddCommGrpCat.{u + 1} ≅
      (etaleRestriction (complementOpenImmersion f i)).sheafPullbackCocontinuous
        AddCommGrpCat.{u + 1}
        (smallEtaleTopology (closedImmersionComplement (inverseImageι f i)))
        (smallEtaleTopology Y) :=
  let j' := complementOpenImmersion f i
  let V := closedImmersionComplement (inverseImageι f i)
  isoWhiskerLeft
      (etaleRestrictionSheaf j' AddCommGrpCat.{u + 1})
      (sheafificationNatIso (smallEtaleTopology V) AddCommGrpCat.{u + 1}) ≪≫
    isoWhiskerRight
      ((etaleRestriction j').sheafPushforwardContinuousCompSheafToPresheafIso
        AddCommGrpCat.{u + 1} (smallEtaleTopology V) (smallEtaleTopology Y))
      (presheafToSheaf (smallEtaleTopology V) AddCommGrpCat.{u + 1})

/-- Component of `inverseImageIsoRestriction` at `G`. -/
theorem inverseImageIsoRestriction_app {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] (G : EtaleSheaf Y) :
    (inverseImageIsoRestriction f i).app G =
      (inverseImageIsoRestriction f i).app G :=
  rfl

/-- The composite `etaleBaseChange f ⋙ spacesEtalePullback g` is continuous. -/
instance etaleBaseChange_comp_spacesEtalePullback_isContinuous
    {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (g : Z ⟶ Y) :
    (etaleBaseChange f ⋙ spacesEtalePullback g).IsContinuous
      (smallEtaleTopology X) (spacesEtaleTopology Z) :=
  Functor.isContinuous_comp (etaleBaseChange f) (spacesEtalePullback g)
    (smallEtaleTopology X) (spacesEtaleTopology Y) (spacesEtaleTopology Z)

/-- Base change along a composite identifies with base change followed by spaces-étale
pullback. -/
def etaleBaseChangeComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    etaleBaseChange (f ≫ g) ≅ etaleBaseChange g ⋙ spacesEtalePullback f :=
  (smallEtaleInclusion_comp_spacesEtalePullback (f ≫ g)).symm ≪≫
    isoWhiskerLeft (smallEtaleInclusion Z) (spacesEtalePullbackComp f g) ≪≫
    isoWhiskerRight (smallEtaleInclusion_comp_spacesEtalePullback g) (spacesEtalePullback f)

/-- Composite pushforward along `j' ≫ f` agrees with the composite of cocontinuous
extension from the open complement and continuous evaluation along the factored
base change `etaleBaseChange f ⋙ spacesEtalePullback j'`. -/
def pushforwardCompIso {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] :
    sheafPushforward AddCommGrpCat.{u + 1} (complementOpenImmersion f i ≫ f) ≅
      (smallEtaleInclusion
            (closedImmersionComplement (inverseImageι f i))).sheafPushforwardCocontinuous
          AddCommGrpCat.{u + 1}
          (smallEtaleTopology (closedImmersionComplement (inverseImageι f i)))
          (spacesEtaleTopology (closedImmersionComplement (inverseImageι f i))) ⋙
        (spacesEtalePullback (complementOpenImmersion f i)).sheafPushforwardContinuous
          AddCommGrpCat.{u + 1} (spacesEtaleTopology Y)
          (spacesEtaleTopology (closedImmersionComplement (inverseImageι f i))) ⋙
        (etaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (smallEtaleTopology X) (spacesEtaleTopology Y) :=
  let j' := complementOpenImmersion f i
  let V := closedImmersionComplement (inverseImageι f i)
  isoWhiskerLeft
      ((smallEtaleInclusion V).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (smallEtaleTopology V) (spacesEtaleTopology V))
      (sheafPushforwardContinuousIso (etaleBaseChangeComp j' f) AddCommGrpCat.{u + 1}
        (smallEtaleTopology X) (spacesEtaleTopology V) ≪≫
        (sheafPushforwardContinuousComp (etaleBaseChange f) (spacesEtalePullback j')
          AddCommGrpCat.{u + 1} (smallEtaleTopology X) (spacesEtaleTopology Y)
          (spacesEtaleTopology V)).symm)

/-- Component of `pushforwardCompIso` at an abelian sheaf on the open complement. -/
theorem pushforwardCompIso_app {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i]
    (H : EtaleSheaf (closedImmersionComplement (inverseImageι f i))) :
    (pushforwardCompIso f i).app H = (pushforwardCompIso f i).app H :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
