/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Square
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward
public import stacks_project.Chap66.Lemma_66_19_9_Exact
public import stacks_project.Chap66.Lemma_66_27_1_Hom
public import stacks_project.Chap69.Lemma_69_6_5_Sections

/-!
# Small étale abelian and derived base-change comparisons of algebraic spaces

The inverse-image identification `g⁻¹ ⋙ (f')⁻¹ ≅ f⁻¹ ⋙ (g')⁻¹` of a cartesian
square of algebraic spaces, the underived mate `g⁻¹ f_* ⟶ f'_* (g')⁻¹`, its
degree-`q` right-derived components, and the bounded-below derived mate
`g⁻¹ Rf_* ⟶ Rf'_* (g')⁻¹` on `D⁺`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.Adjunction
open CategoryTheory.Sheaf
open CategoryTheory.Functor (associator isoWhiskerLeft isoWhiskerRight leftUnitor)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` / `Adjunction.Derived.Plus.right` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `smallEtaleDerivedBaseChangeHom`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

variable {S : Scheme.{u}}

/-- The composite `etaleBaseChange g ⋙ spacesEtalePullback f` is continuous. -/
instance etaleBaseChange_comp_spacesEtalePullback_isContinuous
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (etaleBaseChange g ⋙ spacesEtalePullback f).IsContinuous
      (smallEtaleTopology Z) (spacesEtaleTopology X) :=
  Functor.isContinuous_comp (etaleBaseChange g) (spacesEtalePullback f)
    (smallEtaleTopology Z) (spacesEtaleTopology Y) (spacesEtaleTopology X)

/-- Spaces-étale pullback along a composite is continuous because each factor is. -/
instance spacesEtalePullback_comp_isContinuous {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (spacesEtalePullback g ⋙ spacesEtalePullback f).IsContinuous
      (spacesEtaleTopology Z) (spacesEtaleTopology X) :=
  Functor.isContinuous_comp (spacesEtalePullback g) (spacesEtalePullback f)
    (spacesEtaleTopology Z) (spacesEtaleTopology Y) (spacesEtaleTopology X)

/-- Base change of schemes étale over `Z` along `f ≫ g` identifies with base change along `g`
followed by spaces-étale pullback along `f`. -/
def etaleBaseChangeComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    etaleBaseChange (f ≫ g) ≅ etaleBaseChange g ⋙ spacesEtalePullback f :=
  (smallEtaleInclusion_comp_spacesEtalePullback (f ≫ g)).symm ≪≫
    isoWhiskerLeft (smallEtaleInclusion Z) (spacesEtalePullbackComp f g) ≪≫
    isoWhiskerRight (smallEtaleInclusion_comp_spacesEtalePullback g) (spacesEtalePullback f)

/-- Restricting an abelian sheaf on `X_spaces,étale` to `X_étale` and extending it back
is isomorphic to the identity. -/
def inclusionRestrictExtendIso (X : AlgebraicSpace S)
    [(smallEtaleInclusion X).IsCoverDense (spacesEtaleTopology X)] :
    (smallEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (smallEtaleTopology X) (spacesEtaleTopology X) ⋙
      (smallEtaleInclusion X).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (smallEtaleTopology X) (spacesEtaleTopology X) ≅
    𝟭 (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) :=
  let restrict :=
    (smallEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology X) (spacesEtaleTopology X)
  let extend :=
    (smallEtaleInclusion X).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology X) (spacesEtaleTopology X)
  let adj :=
    (smallEtaleInclusion X).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology X) (spacesEtaleTopology X)
  NatIso.ofComponents
    (fun F ↦
      let i :
          (smallEtaleInclusion X).op ⋙ ((restrict ⋙ extend).obj F).obj ≅
            (smallEtaleInclusion X).op ⋙ F.obj :=
        { hom := (adj.counit.app (restrict.obj F)).hom
          inv := (restrict.map (adj.unit.app F)).hom
          hom_inv_id := sorry
          inv_hom_id := sorry }
      (fullyFaithfulSheafToPresheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}).preimageIso
        { hom := Functor.IsCoverDense.sheafHom i.hom
          inv := Functor.IsCoverDense.sheafHom i.inv
          hom_inv_id := sorry
          inv_hom_id := sorry })
    sorry

/-- Abelian small étale pushforward rewritten through spaces-étale pullback. -/
def sheafPushforwardAbelianFactor {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    sheafPushforwardAbelian f ≅
      (smallEtaleInclusion X).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (smallEtaleTopology X) (spacesEtaleTopology X) ⋙
        (spacesEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (spacesEtaleTopology Y) (spacesEtaleTopology X) ⋙
        (smallEtaleInclusion Y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (smallEtaleTopology Y) (spacesEtaleTopology Y) :=
  isoWhiskerLeft
    ((smallEtaleInclusion X).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology X) (spacesEtaleTopology X))
    ((Functor.sheafPushforwardContinuousIso
          (smallEtaleInclusion_comp_spacesEtalePullback f) AddCommGrpCat.{u + 1}
          (smallEtaleTopology Y) (spacesEtaleTopology X)).symm ≪≫
      (Functor.sheafPushforwardContinuousComp (smallEtaleInclusion Y)
          (spacesEtalePullback f) AddCommGrpCat.{u + 1} (smallEtaleTopology Y)
          (spacesEtaleTopology Y) (spacesEtaleTopology X)).symm)

/-- Continuous abelian pushforward along spaces-étale pullback respects composition. -/
def spacesEtaleAbelianPushforwardComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (spacesEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (spacesEtaleTopology Y) (spacesEtaleTopology X) ⋙
      (spacesEtalePullback g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (spacesEtaleTopology Z) (spacesEtaleTopology Y) ≅
      (spacesEtalePullback (f ≫ g)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (spacesEtaleTopology Z) (spacesEtaleTopology X) :=
  (spacesEtalePullback g).sheafPushforwardContinuousComp (spacesEtalePullback f)
      AddCommGrpCat.{u + 1} (spacesEtaleTopology Z) (spacesEtaleTopology Y)
      (spacesEtaleTopology X) ≪≫
    Functor.sheafPushforwardContinuousIso (spacesEtalePullbackComp f g).symm
      AddCommGrpCat.{u + 1} (spacesEtaleTopology Z) (spacesEtaleTopology X)

/-- Abelian small étale direct image along a composite is the composite of the direct images. -/
def sheafPushforwardAbelian_comp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [(smallEtaleInclusion Y).IsCoverDense (spacesEtaleTopology Y)] :
    sheafPushforwardAbelian f ⋙ sheafPushforwardAbelian g ≅
      sheafPushforwardAbelian (f ≫ g) :=
  let iX :=
    (smallEtaleInclusion X).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology X) (spacesEtaleTopology X)
  let pF :=
    (spacesEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (spacesEtaleTopology Y) (spacesEtaleTopology X)
  let iY :=
    (smallEtaleInclusion Y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology Y) (spacesEtaleTopology Y)
  let pG :=
    (spacesEtalePullback g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (spacesEtaleTopology Z) (spacesEtaleTopology Y)
  let iZ :=
    (smallEtaleInclusion Z).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology Z) (spacesEtaleTopology Z)
  isoWhiskerRight (sheafPushforwardAbelianFactor f) (sheafPushforwardAbelian g) ≪≫
    associator iX (pF ⋙ iY) (sheafPushforwardAbelian g) ≪≫
    isoWhiskerLeft iX (associator pF iY (sheafPushforwardAbelian g)) ≪≫
    isoWhiskerLeft (iX ⋙ pF) (isoWhiskerLeft iY (sheafPushforwardAbelianFactor g)) ≪≫
    isoWhiskerLeft (iX ⋙ pF)
      (associator iY
          ((smallEtaleInclusion Y).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
            (smallEtaleTopology Y) (spacesEtaleTopology Y))
          (pG ⋙ iZ) ≪≫
        isoWhiskerRight (inclusionRestrictExtendIso Y) (pG ⋙ iZ) ≪≫
        leftUnitor (pG ⋙ iZ)) ≪≫
    isoWhiskerLeft iX
      (associator pF pG iZ ≪≫ isoWhiskerRight (spacesEtaleAbelianPushforwardComp f g) iZ) ≪≫
    (sheafPushforwardAbelianFactor (f ≫ g)).symm

/-- Inverse image of abelian small-étale sheaves along a composite is the composite inverse
image. -/
def sheafInverseImage_comp {X Y Z : AlgebraicSpace S} (p : Y ⟶ Z) (q : X ⟶ Y)
    [(smallEtaleInclusion Y).IsCoverDense (spacesEtaleTopology Y)] :
    sheafInverseImage AddCommGrpCat.{u + 1} p ⋙
        sheafInverseImage AddCommGrpCat.{u + 1} q ≅
      sheafInverseImage AddCommGrpCat.{u + 1} (q ≫ p) :=
  leftAdjointCompIso (sheafInverseImageAdjunction p) (sheafInverseImageAdjunction q)
    (sheafInverseImageAdjunction (q ≫ p)) (sheafPushforwardAbelian_comp q p)

section

variable {X Y X' Y' : AlgebraicSpace S}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable [(smallEtaleInclusion Y).IsCoverDense (spacesEtaleTopology Y)]
variable [(smallEtaleInclusion X).IsCoverDense (spacesEtaleTopology X)]

/-- The inverse-image identification `g⁻¹ ⋙ (f')⁻¹ ≅ f⁻¹ ⋙ (g')⁻¹` of a cartesian
square of algebraic spaces. -/
def smallEtaleAbelianInverseImageSquare :
    sheafInverseImage AddCommGrpCat.{u + 1} g ⋙
        sheafInverseImage AddCommGrpCat.{u + 1} f' ≅
      sheafInverseImage AddCommGrpCat.{u + 1} f ⋙
        sheafInverseImage AddCommGrpCat.{u + 1} g' :=
  sheafInverseImage_comp g f' ≪≫
    eqToIso
      (congrArg (fun h : X' ⟶ Y ↦ sheafInverseImage AddCommGrpCat.{u + 1} h)
        h_cart.w.symm) ≪≫
    (sheafInverseImage_comp f g').symm

/-- `smallEtaleAbelianInverseImageSquare` is the composite of `sheafInverseImage_comp`
with the commutativity of the cartesian square. -/
theorem smallEtaleAbelianInverseImageSquare_eq :
    smallEtaleAbelianInverseImageSquare f g f' g' h_cart =
      sheafInverseImage_comp g f' ≪≫
        eqToIso
          (congrArg (fun h : X' ⟶ Y ↦ sheafInverseImage AddCommGrpCat.{u + 1} h)
            h_cart.w.symm) ≪≫
        (sheafInverseImage_comp f g').symm :=
  sorry

/-- The underived mate `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of a cartesian square of algebraic spaces. -/
def smallEtaleAbelianBaseChange :
    sheafPushforwardAbelian f ⋙ sheafInverseImage AddCommGrpCat.{u + 1} g ⟶
      sheafInverseImage AddCommGrpCat.{u + 1} g' ⋙ sheafPushforwardAbelian f' :=
  DerivedBaseChange.map (sheafInverseImageAdjunction f) (sheafInverseImageAdjunction f')
    (smallEtaleAbelianInverseImageSquare f g f' g' h_cart)

/-- `smallEtaleAbelianBaseChange` is the right mate of the inverse-image square. -/
theorem smallEtaleAbelianBaseChange_eq :
    smallEtaleAbelianBaseChange f g f' g' h_cart =
      DerivedBaseChange.map (sheafInverseImageAdjunction f)
        (sheafInverseImageAdjunction f')
        (smallEtaleAbelianInverseImageSquare f g f' g' h_cart) :=
  sorry

variable (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})

/-- The objectwise underived comparison `g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F`. -/
def smallEtaleAbelianBaseChangeHom :
    (sheafInverseImage AddCommGrpCat.{u + 1} g).obj
      ((sheafPushforwardAbelian f).obj F) ⟶
      (sheafPushforwardAbelian f').obj
        ((sheafInverseImage AddCommGrpCat.{u + 1} g').obj F) :=
  (smallEtaleAbelianBaseChange f g f' g' h_cart).app F

/-- `smallEtaleAbelianBaseChangeHom` is the component of `smallEtaleAbelianBaseChange`. -/
theorem smallEtaleAbelianBaseChangeHom_eq :
    smallEtaleAbelianBaseChangeHom f g f' g' h_cart F =
      (smallEtaleAbelianBaseChange f g f' g' h_cart).app F :=
  sorry

variable [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology X') AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology Y') AddCommGrpCat.{u + 1}]
variable [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (smallEtaleTopology Y') AddCommGrpCat.{u + 1})]
variable [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [HasInjectiveResolutions (Sheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1})]
variable [(sheafPushforwardAbelian f).Additive]
variable [(sheafPushforwardAbelian f').Additive]
variable [(sheafInverseImage AddCommGrpCat.{u + 1} g).Additive]
variable [(sheafInverseImage AddCommGrpCat.{u + 1} g').Additive]

/-- Degree-`q` comparison `g⁻¹ R^q f_* F ⟶ R^q f'_* (g')⁻¹ F`, obtained by
right-deriving the underived mate. -/
def higherDirectImage_baseChangeHom (q : ℕ) :
    (((sheafPushforwardAbelian f ⋙
          sheafInverseImage AddCommGrpCat.{u + 1} g :
          Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
            Sheaf (smallEtaleTopology Y') AddCommGrpCat.{u + 1}).rightDerived q).obj F) ⟶
      (((sheafInverseImage AddCommGrpCat.{u + 1} g' ⋙
          sheafPushforwardAbelian f' :
          Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
            Sheaf (smallEtaleTopology Y') AddCommGrpCat.{u + 1}).rightDerived q).obj F) :=
  (NatTrans.rightDerived (smallEtaleAbelianBaseChange f g f' g' h_cart) q).app F

/-- `higherDirectImage_baseChangeHom` is the degree-`q` right-derived component of the
underived mate. -/
theorem higherDirectImage_baseChangeHom_eq (q : ℕ) :
    higherDirectImage_baseChangeHom f g f' g' h_cart F q =
      (NatTrans.rightDerived (smallEtaleAbelianBaseChange f g f' g' h_cart) q).app F :=
  sorry

/-- Exact inverse image `f_small⁻¹` on abelian small-étale sheaves. -/
abbrev smallEtaleInverseExact {A B : AlgebraicSpace S} (h : A ⟶ B) :
    Sheaf (smallEtaleTopology B) AddCommGrpCat.{u + 1} ⥤ₑ
      Sheaf (smallEtaleTopology A) AddCommGrpCat.{u + 1} :=
  ExactFunctor.of (sheafInverseImage AddCommGrpCat.{u + 1} h)

variable [HasDerivedCategory (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology Y') AddCommGrpCat.{u + 1})]
variable [(sheafPushforwardAbelian f).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))]
variable [(sheafPushforwardAbelian f').toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1}))]

/-- Bounded-below derived inverse image `f_small⁻¹` on `D⁺`. -/
abbrev smallEtaleDerivedInverseImage {A B : AlgebraicSpace S} (h : A ⟶ B)
    [Abelian (Sheaf (smallEtaleTopology A) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology B) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (Sheaf (smallEtaleTopology A) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (Sheaf (smallEtaleTopology B) AddCommGrpCat.{u + 1})] :
    DerivedCategory.Plus (Sheaf (smallEtaleTopology B) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (smallEtaleTopology A) AddCommGrpCat.{u + 1}) :=
  Adjunction.Derived.Plus.left (smallEtaleInverseExact h)

/-- Bounded-below derived pushforward `Rf_small,*` on `D⁺`. -/
abbrev smallEtaleDerivedPushforward {A B : AlgebraicSpace S} (h : A ⟶ B)
    [Abelian (Sheaf (smallEtaleTopology A) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology B) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (Sheaf (smallEtaleTopology A) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (Sheaf (smallEtaleTopology B) AddCommGrpCat.{u + 1})]
    [(sheafPushforwardAbelian h).Additive]
    [(sheafPushforwardAbelian h).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (smallEtaleTopology A) AddCommGrpCat.{u + 1}))] :
    DerivedCategory.Plus (Sheaf (smallEtaleTopology A) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (smallEtaleTopology B) AddCommGrpCat.{u + 1}) :=
  Adjunction.Derived.Plus.right (sheafPushforwardAbelian h)

/-- The bounded-below inverse-image square
`g⁻¹ ⋙ (f')⁻¹ ≅ f⁻¹ ⋙ (g')⁻¹` on `D⁺`. -/
def smallEtaleDerivedInverseImageSquare :
    smallEtaleDerivedInverseImage g ⋙ smallEtaleDerivedInverseImage f' ≅
      smallEtaleDerivedInverseImage f ⋙ smallEtaleDerivedInverseImage g' :=
  ExactFunctor.Derived.Plus.squareIso
    (smallEtaleInverseExact g) (smallEtaleInverseExact f')
    (smallEtaleInverseExact f) (smallEtaleInverseExact g')
    ((exactFunctor _ _).isoMk
      (smallEtaleAbelianInverseImageSquare f g f' g' h_cart))

/-- The canonical derived base-change transformation
`g⁻¹ Rf_* ⟶ Rf'_* (g')⁻¹` on `D⁺`. -/
def smallEtaleDerivedBaseChange :
    smallEtaleDerivedPushforward f ⋙ smallEtaleDerivedInverseImage g ⟶
      smallEtaleDerivedInverseImage g' ⋙ smallEtaleDerivedPushforward f' :=
  DerivedBaseChange.map
    (Adjunction.Derived.Plus.adjunction (smallEtaleInverseExact f)
      (sheafPushforwardAbelian f) (sheafInverseImageAdjunction f))
    (Adjunction.Derived.Plus.adjunction (smallEtaleInverseExact f')
      (sheafPushforwardAbelian f') (sheafInverseImageAdjunction f'))
    (smallEtaleDerivedInverseImageSquare f g f' g' h_cart)

/-- `smallEtaleDerivedBaseChange` is the mate of `smallEtaleDerivedInverseImageSquare`. -/
theorem smallEtaleDerivedBaseChange_eq :
    smallEtaleDerivedBaseChange f g f' g' h_cart =
      DerivedBaseChange.map
        (Adjunction.Derived.Plus.adjunction (smallEtaleInverseExact f)
          (sheafPushforwardAbelian f) (sheafInverseImageAdjunction f))
        (Adjunction.Derived.Plus.adjunction (smallEtaleInverseExact f')
          (sheafPushforwardAbelian f') (sheafInverseImageAdjunction f'))
        (smallEtaleDerivedInverseImageSquare f g f' g' h_cart) :=
  sorry

variable (E : DerivedCategory.Plus
    (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))

/-- The component of canonical derived base change at an object of `D⁺(X_étale)`. -/
def smallEtaleDerivedBaseChangeHom :
    (smallEtaleDerivedInverseImage g).obj
      ((smallEtaleDerivedPushforward f).obj E) ⟶
      (smallEtaleDerivedPushforward f').obj
        ((smallEtaleDerivedInverseImage g').obj E) :=
  (smallEtaleDerivedBaseChange f g f' g' h_cart).app E

/-- `smallEtaleDerivedBaseChangeHom` is the component of `smallEtaleDerivedBaseChange`. -/
theorem smallEtaleDerivedBaseChangeHom_eq :
    smallEtaleDerivedBaseChangeHom f g f' g' h_cart E =
      (smallEtaleDerivedBaseChange f g f' g' h_cart).app E :=
  sorry

end

section

variable {X Y Y' : AlgebraicSpace S}
variable (f : X ⟶ Y) (g : Y' ⟶ Y)
variable [(smallEtaleInclusion Y).IsCoverDense (spacesEtaleTopology Y)]
variable [(smallEtaleInclusion X).IsCoverDense (spacesEtaleTopology X)]
variable [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology Y') AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology (pullback g f)) AddCommGrpCat.{u + 1}]
variable [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (smallEtaleTopology Y') AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (smallEtaleTopology (pullback g f)) AddCommGrpCat.{u + 1})]
variable [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology Y') AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology (pullback g f)) AddCommGrpCat.{u + 1})]
variable [(sheafPushforwardAbelian f).Additive]
variable [(sheafPushforwardAbelian (pullback.fst g f)).Additive]
variable [(sheafPushforwardAbelian f).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))]
variable [(sheafPushforwardAbelian (pullback.fst g f)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (smallEtaleTopology (pullback g f)) AddCommGrpCat.{u + 1}))]
variable [(sheafInverseImage AddCommGrpCat.{u + 1} g).Additive]
variable [(sheafInverseImage AddCommGrpCat.{u + 1} (pullback.snd g f)).Additive]

variable (E : DerivedCategory.Plus
    (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))

/-- The derived comparison morphism of the chosen fibre product `Y' ×_Y X`. -/
def smallEtaleDerivedBaseChangeHom_pullback :
    (smallEtaleDerivedInverseImage g).obj
      ((smallEtaleDerivedPushforward f).obj E) ⟶
      (smallEtaleDerivedPushforward (pullback.fst g f)).obj
        ((smallEtaleDerivedInverseImage (pullback.snd g f)).obj E) :=
  smallEtaleDerivedBaseChangeHom f g (pullback.fst g f) (pullback.snd g f)
    (IsPullback.of_hasPullback g f).flip E

/-- `smallEtaleDerivedBaseChangeHom_pullback` is `smallEtaleDerivedBaseChangeHom` at the
chosen pullback square. -/
theorem smallEtaleDerivedBaseChangeHom_pullback_eq :
    smallEtaleDerivedBaseChangeHom_pullback f g E =
      smallEtaleDerivedBaseChangeHom f g (pullback.fst g f) (pullback.snd g f)
        (IsPullback.of_hasPullback g f).flip E :=
  sorry

end

end AlgebraicGeometry.AlgebraicSpace
