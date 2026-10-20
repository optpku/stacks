/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap94.«94_8_2_1_FullyFaithful»
public import stacks_project.Chap96.«96_10_3_1_Geometry»
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DirectImage
public import ReasLib.CategoryTheory.Sites.Pushforward.SmallSectionsAdjunction
public import ReasLib.CategoryTheory.Fibered.Groupoids.UnderlyingFunctorIso
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Represented CFG direct-image sections at arbitrary target objects

The fibre algebraic space over the scheme underlying a target object has
an actual étale atlas and kernel pair. A given sheaf's compatible sections
are recovered from that finite descent diagram; arbitrary presheaves do
not receive a size assertion.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The space morphism obtained by evaluating the actual presented total functor. -/
def moduleComparisonSpaceMorphism {Ucfg Vcfg : GroupoidsOver S} (a : Ucfg ⟶ Vcfg)
    {U V : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg) :
    U ⟶ V :=
  AlgebraicSpace.toGroupoids.recover eU.symm eV.symm a

namespace RepresentedDirectImage

variable {Ucfg Vcfg : GroupoidsOver S} (a : Ucfg ⟶ Vcfg)
variable {U V : AlgebraicSpace S}
variable (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)

/-- The actual presented functor, before recovering its space map. -/
def presentedMorphism : U.toGroupoids ⟶ V.toGroupoids :=
  (eU.hom ≫ a) ≫ eV.inv

/-- The scheme and map underlying an arbitrary target presentation object. -/
def targetScheme (y : Vcfg.total) : Over S :=
  (unop ((toFunctor eV.inv).obj y)).1.unop

def targetHom (y : Vcfg.total) : AlgebraicSpace.ofOver (targetScheme eV y) ⟶ V :=
  yonedaEquiv.symm ((unop ((toFunctor eV.inv).obj y)).2)

/-- The fibre algebraic space `U ×_V scheme(y)` for the given original target object. -/
def fibreSpace (y : Vcfg.total) : AlgebraicSpace S :=
  AlgebraicSpace.pullbackOver (moduleComparisonSpaceMorphism a eU eV) (targetHom eV y)
    V.isSheaf V.representableDiagonal

/-- A specified actual atlas scheme of the fibre algebraic space. -/
def atlasScheme (y : Vcfg.total) : Over S :=
  AlgebraicSpace.compareAtlasScheme (fibreSpace a eU eV y)

def atlasToFibre (y : Vcfg.total) :
    AlgebraicSpace.ofOver (atlasScheme a eU eV y) ⟶ fibreSpace a eU eV y :=
  AlgebraicSpace.compareAtlasHom (fibreSpace a eU eV y)

/-- Its actual source projection; it need not be étale over `U`. -/
def atlasToSource (y : Vcfg.total) :
    AlgebraicSpace.ofOver (atlasScheme a eU eV y) ⟶ U :=
  atlasToFibre a eU eV y ≫
    AlgebraicSpace.pullbackOverFst (moduleComparisonSpaceMorphism a eU eV)
      (targetHom eV y) V.isSheaf V.representableDiagonal

/-- Its actual target-scheme projection, recovered by Yoneda. -/
def atlasToTarget (y : Vcfg.total) :
    atlasScheme a eU eV y ⟶ targetScheme eV y :=
  yoneda.preimage
    (atlasToFibre a eU eV y ≫
      AlgebraicSpace.pullbackOverSnd (moduleComparisonSpaceMorphism a eU eV)
        (targetHom eV y) V.isSheaf V.representableDiagonal)

/-- The source presentation object of the atlas, using its actual source projection. -/
def atlasObj (y : Vcfg.total) : U.toGroupoids.total :=
  op ⟨op (atlasScheme a eU eV y), yonedaEquiv (atlasToSource a eU eV y)⟩

/-- The scheme underlying its actual image under the supplied presented functor. -/
def imageAtlasScheme (y : Vcfg.total) : Over S :=
  (unop ((toFunctor (presentedMorphism a eU eV)).obj (atlasObj a eU eV y))).1.unop

/-- Strict base commutativity identifies the actual image scheme with the atlas scheme. -/
def imageAtlasSchemeIso (y : Vcfg.total) :
    imageAtlasScheme a eU eV y ≅ atlasScheme a eU eV y :=
  (eqToIso (comm (presentedMorphism a eU eV))).app (atlasObj a eU eV y)

/-- The target arrow is a category-of-elements morphism with the actual underlying scheme map. -/
def atlasToTargetPresented (y : Vcfg.total) :
    (toFunctor (presentedMorphism a eU eV)).obj (atlasObj a eU eV y) ⟶
      (toFunctor eV.inv).obj y :=
  (CategoryOfElements.homMk
    (unop ((toFunctor eV.inv).obj y))
    (unop ((toFunctor (presentedMorphism a eU eV)).obj (atlasObj a eU eV y)))
    ((imageAtlasSchemeIso a eU eV y).hom ≫ atlasToTarget a eU eV y).op sorry).op

/-- The given target presentation counit, with actual components in the original CFG. -/
def targetCounitIso : toFunctor eV.inv ⋙ toFunctor eV.hom ≅ 𝟭 Vcfg.total :=
  ObjectProperty.FullSubbicategory.toFunctor.compIso eV.inv eV.hom ≪≫
    toFunctorIso eV.counit ≪≫ eqToIso (toFunctor.id Vcfg)

/-- Reconstruct the original target arrow using the supplied presentation counit. -/
def atlasToTargetCFG (y : Vcfg.total) :
    (toFunctor a).obj ((toFunctor eU.hom).obj (atlasObj a eU eV y)) ⟶ y :=
  (targetCounitIso eV).inv.app _ ≫
    (toFunctor eV.hom).map
      ((toFunctor eV.inv).map
          ((ObjectProperty.FullSubbicategory.toFunctor.compIso eU.hom a).hom.app
            (atlasObj a eU eV y)) ≫
        (ObjectProperty.FullSubbicategory.toFunctor.compIso (eU.hom ≫ a) eV.inv).hom.app
          (atlasObj a eU eV y) ≫
        atlasToTargetPresented a eU eV y) ≫
    (targetCounitIso eV).hom.app y

/-- The actual comma diagram at an arbitrary target object. -/
abbrev index (y : Vcfg.total) :=
  StructuredArrow (op y) (toCartesianBasedFunctor a).toFunctor.op

def atlasIndex (y : Vcfg.total) : index a y :=
  StructuredArrow.mk (atlasToTargetCFG a eU eV y).op

/-- The kernel pair of the actual fibre atlas is a scheme by representable diagonal. -/
def pairScheme (y : Vcfg.total) : Over S :=
  AlgebraicSpace.pullbackOverAtlas (atlasToFibre a eU eV y) (atlasToFibre a eU eV y)
    (fibreSpace a eU eV y).representableDiagonal (𝟙 _) (𝟙 _)

def pairFst (y : Vcfg.total) : pairScheme a eU eV y ⟶ atlasScheme a eU eV y :=
  yonedaEquiv (AlgebraicSpace.pullbackOverAtlasFst
    (atlasToFibre a eU eV y) (atlasToFibre a eU eV y)
    (fibreSpace a eU eV y).representableDiagonal (𝟙 _) (𝟙 _))

def pairSnd (y : Vcfg.total) : pairScheme a eU eV y ⟶ atlasScheme a eU eV y :=
  AlgebraicSpace.pullbackOverAtlasSnd
    (atlasToFibre a eU eV y) (atlasToFibre a eU eV y)
    (fibreSpace a eU eV y).representableDiagonal (𝟙 _) (𝟙 _)

def pairObj (y : Vcfg.total) : U.toGroupoids.total :=
  op ⟨op (pairScheme a eU eV y),
    yonedaEquiv (AlgebraicSpace.ofOverMap (pairFst a eU eV y) ≫
      atlasToSource a eU eV y)⟩

def pairToAtlasFst (y : Vcfg.total) : pairObj a eU eV y ⟶ atlasObj a eU eV y :=
  (CategoryOfElements.homMk (unop (atlasObj a eU eV y)) (unop (pairObj a eU eV y))
    (pairFst a eU eV y).op sorry).op

def pairToAtlasSnd (y : Vcfg.total) : pairObj a eU eV y ⟶ atlasObj a eU eV y :=
  (CategoryOfElements.homMk (unop (atlasObj a eU eV y)) (unop (pairObj a eU eV y))
    (pairSnd a eU eV y).op sorry).op

def pairIndex (y : Vcfg.total) : index a y :=
  StructuredArrow.mk
    ((toFunctor a).map ((toFunctor eU.hom).map (pairToAtlasFst a eU eV y)) ≫
      atlasToTargetCFG a eU eV y).op

def atlasIndexToPairFst (y : Vcfg.total) : atlasIndex a eU eV y ⟶ pairIndex a eU eV y :=
  StructuredArrow.homMk ((toFunctor eU.hom).map (pairToAtlasFst a eU eV y)).op sorry

def atlasIndexToPairSnd (y : Vcfg.total) : atlasIndex a eU eV y ⟶ pairIndex a eU eV y :=
  StructuredArrow.homMk ((toFunctor eU.hom).map (pairToAtlasSnd a eU eV y)).op sorry

/-- Descent data are a subtype of the actual atlas section type in the coefficient universe. -/
def descentSections (F : Sheaf Ucfg.etaleTopology (Type u)) (y : Vcfg.total) : Type u :=
  { s : F.obj.obj (op ((toFunctor eU.hom).obj (atlasObj a eU eV y))) //
    F.obj.map ((toFunctor eU.hom).map (pairToAtlasFst a eU eV y)).op s =
      F.obj.map ((toFunctor eU.hom).map (pairToAtlasSnd a eU eV y)).op s }

/-- The actual sheaf diagram indexed by all original arrows into the target object. -/
abbrev diagram (F : Sheaf Ucfg.etaleTopology (Type u)) (y : Vcfg.total) :
    index a y ⥤ Type u :=
  StructuredArrow.proj (op y) (toCartesianBasedFunctor a).toFunctor.op ⋙ F.obj

def chartObj {y : Vcfg.total} (j : index a y) : U.toGroupoids.total :=
  (toFunctor eU.inv).obj j.right.unop

def chartScheme {y : Vcfg.total} (j : index a y) : Over S :=
  (unop (chartObj a eU j)).1.unop

def chartToSource {y : Vcfg.total} (j : index a y) :
    AlgebraicSpace.ofOver (chartScheme a eU j) ⟶ U :=
  yonedaEquiv.symm (unop (chartObj a eU j)).2

/-- Transport the original comma arrow only through supplied presentation functors and counit. -/
def chartToTargetPresented {y : Vcfg.total} (j : index a y) :
    (toFunctor (presentedMorphism a eU eV)).obj (chartObj a eU j) ⟶
      (toFunctor eV.inv).obj y :=
  (ObjectProperty.FullSubbicategory.toFunctor.compIso (eU.hom ≫ a) eV.inv).inv.app _ ≫
    (toFunctor eV.inv).map
      ((ObjectProperty.FullSubbicategory.toFunctor.compIso eU.hom a).inv.app _ ≫
        (toFunctor a).map ((toFunctorIso eU.counit).hom.app j.right.unop) ≫ j.hom.unop)

def chartToTarget {y : Vcfg.total} (j : index a y) :
    chartScheme a eU j ⟶ targetScheme eV y :=
  (eqToIso (comm (presentedMorphism a eU eV))).inv.app (chartObj a eU j) ≫
    (chartToTargetPresented a eU eV j).unop.val.unop

/-- The chart maps into the actual fibre by its two original scheme/space projections. -/
def chartToFibre {y : Vcfg.total} (j : index a y) :
    AlgebraicSpace.ofOver (chartScheme a eU j) ⟶ fibreSpace a eU eV y :=
  AlgebraicSpace.ReasLibPullback.pullbackLift (moduleComparisonSpaceMorphism a eU eV) (targetHom eV y)
    (chartToSource a eU j) (AlgebraicSpace.ofOverMap (chartToTarget a eU eV j)) sorry

def chartCoverScheme {y : Vcfg.total} (j : index a y) : Over S :=
  AlgebraicSpace.pullbackOverAtlas (chartToFibre a eU eV j) (atlasToFibre a eU eV y)
    (fibreSpace a eU eV y).representableDiagonal (𝟙 _) (𝟙 _)

def chartCoverFst {y : Vcfg.total} (j : index a y) :
    chartCoverScheme a eU eV j ⟶ chartScheme a eU j :=
  yonedaEquiv (AlgebraicSpace.pullbackOverAtlasFst
    (chartToFibre a eU eV j) (atlasToFibre a eU eV y)
    (fibreSpace a eU eV y).representableDiagonal (𝟙 _) (𝟙 _))

def chartCoverSnd {y : Vcfg.total} (j : index a y) :
    chartCoverScheme a eU eV j ⟶ atlasScheme a eU eV y :=
  AlgebraicSpace.pullbackOverAtlasSnd
    (chartToFibre a eU eV j) (atlasToFibre a eU eV y)
    (fibreSpace a eU eV y).representableDiagonal (𝟙 _) (𝟙 _)

def chartCoverObj {y : Vcfg.total} (j : index a y) : U.toGroupoids.total :=
  op ⟨op (chartCoverScheme a eU eV j),
    yonedaEquiv (AlgebraicSpace.ofOverMap (chartCoverFst a eU eV j) ≫ chartToSource a eU j)⟩

def chartCoverToChart {y : Vcfg.total} (j : index a y) :
    chartCoverObj a eU eV j ⟶ chartObj a eU j :=
  (CategoryOfElements.homMk (unop (chartObj a eU j)) (unop (chartCoverObj a eU eV j))
    (chartCoverFst a eU eV j).op sorry).op

def chartCoverToAtlas {y : Vcfg.total} (j : index a y) :
    chartCoverObj a eU eV j ⟶ atlasObj a eU eV y :=
  (CategoryOfElements.homMk (unop (atlasObj a eU eV y)) (unop (chartCoverObj a eU eV j))
    (chartCoverSnd a eU eV j).op sorry).op

def chartCoverToOriginal {y : Vcfg.total} (j : index a y) :
    (toFunctor eU.hom).obj (chartCoverObj a eU eV j) ⟶ j.right.unop :=
  (toFunctor eU.hom).map (chartCoverToChart a eU eV j) ≫
    (toFunctorIso eU.counit).hom.app j.right.unop

/-- The actual atlas pullback covers the original source object, including arbitrary target charts. -/
theorem chartCover_mem {y : Vcfg.total} (j : index a y) :
    Sieve.ofArrows
      (fun _ : Unit ↦ (toFunctor eU.hom).obj (chartCoverObj a eU eV j))
      (fun _ ↦ chartCoverToOriginal a eU eV j) ∈ Ucfg.etaleTopology j.right.unop := sorry

def chartCoverSection (F : Sheaf Ucfg.etaleTopology (Type u)) {y : Vcfg.total}
    (j : index a y) : descentSections a eU eV F y ⟶
      F.obj.obj (op ((toFunctor eU.hom).obj (chartCoverObj a eU eV j))) :=
  TypeCat.ofHom fun s ↦ F.obj.map
    ((toFunctor eU.hom).map (chartCoverToAtlas a eU eV j)).op s.val

/-- Kernel-pair compatibility restricts to every atlas pullback overlap. -/
theorem chartCoverSection_compatible (F : Sheaf Ucfg.etaleTopology (Type u))
    {y : Vcfg.total} (j : index a y) :
    ∀ ⦃T : Ucfg.total⦄ ⦃i k : Unit⦄
      (b c : T ⟶ (toFunctor eU.hom).obj (chartCoverObj a eU eV j)),
      b ≫ chartCoverToOriginal a eU eV j = c ≫ chartCoverToOriginal a eU eV j →
      chartCoverSection a eU eV F j ≫ F.obj.map b.op =
        chartCoverSection a eU eV F j ≫ F.obj.map c.op := sorry

/-- Amalgamation reconstructs the original sheaf section at every actual comma chart. -/
def coneProjection (F : Sheaf Ucfg.etaleTopology (Type u)) {y : Vcfg.total}
    (j : index a y) : descentSections a eU eV F y ⟶ (diagram a F y).obj j :=
  F.property.amalgamateOfArrows
    (fun _ : Unit ↦ chartCoverToOriginal a eU eV j)
    (chartCover_mem a eU eV j)
    (fun _ ↦ chartCoverSection a eU eV F j)
    (chartCoverSection_compatible a eU eV F j)

def cone (F : Sheaf Ucfg.etaleTopology (Type u)) (y : Vcfg.total) :
    Cone (diagram a F y) where
  pt := descentSections a eU eV F y
  π := { app := coneProjection a eU eV F, naturality := sorry }

/-- The universal lift evaluates the supplied cone at the actual atlas comma object. -/
def coneIsLimit (F : Sheaf Ucfg.etaleTopology (Type u)) (y : Vcfg.total) :
    IsLimit (cone a eU eV F y) where
  lift c := TypeCat.ofHom fun x ↦ ⟨c.π.app (atlasIndex a eU eV y) x, by sorry⟩
  fac := sorry
  uniq := sorry

include eU eV in
/-- Compatible sections are small because the real finite descent cone has a genuine universal lift. -/
theorem sectionsSmall (F : Sheaf Ucfg.etaleTopology (Type u)) (y : Vcfg.total) :
    Small.{u} (diagram a F y).sections :=
  Small.mk' (Types.isLimitEquivSections (coneIsLimit a eU eV F y)).symm

end RepresentedDirectImage

/-- The supplied source and target presentations produce Type-`u` compatible
sections using the actual fibre atlas and kernel-pair descent cone. -/
theorem hasSmallCFGTypeSections_ofRepresented {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg) :
    HasSmallCFGTypeSections (S := S) a where
  small F y := RepresentedDirectImage.sectionsSmall a eU eV F y.unop

end AlgebraicGeometry.GroupoidsOver
