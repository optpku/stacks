/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Square
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.SpacesHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.InverseImage.Exact

/-!
# Small étale abelian and derived base-change comparisons of algebraic spaces

The inverse-image identification `g⁻¹ ⋙ (f')⁻¹ ≅ f⁻¹ ⋙ (g')⁻¹` of a cartesian
square of algebraic spaces, the underived mate `g⁻¹ f_* ⟶ f'_* (g')⁻¹`, its
degree-`q` derivatives between composite functors, and the bounded-below derived mate
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

/-- Abelian small étale pushforward rewritten through spaces-étale pullback. -/
private def sheafPushforwardAbelianFactor {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    sheafPushforwardAbelian f ≅
      (smallEtaleToSpaces X).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (smallEtaleTopology X) (spacesEtaleTopology X) ⋙
        (spacesEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (spacesEtaleTopology Y) (spacesEtaleTopology X) ⋙
        (smallEtaleToSpaces Y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (smallEtaleTopology Y) (spacesEtaleTopology Y) :=
  isoWhiskerLeft
    ((smallEtaleToSpaces X).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology X) (spacesEtaleTopology X))
    (Functor.sheafPushforwardContinuousComp'
      (smallEtaleInclusion_comp_spacesEtalePullback f) AddCommGrpCat.{u + 1}
      (smallEtaleTopology Y) (spacesEtaleTopology Y) (spacesEtaleTopology X)).symm

/-- Continuous abelian pushforward along spaces-étale pullback respects composition. -/
private def spacesEtaleAbelianPushforwardComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (spacesEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (spacesEtaleTopology Y) (spacesEtaleTopology X) ⋙
      (spacesEtalePullback g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (spacesEtaleTopology Z) (spacesEtaleTopology Y) ≅
      (spacesEtalePullback (f ≫ g)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (spacesEtaleTopology Z) (spacesEtaleTopology X) :=
  Functor.sheafPushforwardContinuousComp' (spacesEtalePullbackComp f g).symm
    AddCommGrpCat.{u + 1} (spacesEtaleTopology Z) (spacesEtaleTopology Y)
    (spacesEtaleTopology X)

/-- Abelian small étale direct image along a composite is the composite of the direct images. -/
@[no_expose] def sheafPushforwardAbelian_comp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [(smallEtaleToSpaces Y).IsCoverDense (spacesEtaleTopology Y)] :
    sheafPushforwardAbelian f ⋙ sheafPushforwardAbelian g ≅
      sheafPushforwardAbelian (f ≫ g) :=
  let iX :=
    (smallEtaleToSpaces X).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology X) (spacesEtaleTopology X)
  let pF :=
    (spacesEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (spacesEtaleTopology Y) (spacesEtaleTopology X)
  let iY :=
    (smallEtaleToSpaces Y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology Y) (spacesEtaleTopology Y)
  let pG :=
    (spacesEtalePullback g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (spacesEtaleTopology Z) (spacesEtaleTopology Y)
  let iZ :=
    (smallEtaleToSpaces Z).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology Z) (spacesEtaleTopology Z)
  isoWhiskerRight (sheafPushforwardAbelianFactor f) (sheafPushforwardAbelian g) ≪≫
    associator iX (pF ⋙ iY) (sheafPushforwardAbelian g) ≪≫
    isoWhiskerLeft iX (associator pF iY (sheafPushforwardAbelian g)) ≪≫
    isoWhiskerLeft (iX ⋙ pF) (isoWhiskerLeft iY (sheafPushforwardAbelianFactor g)) ≪≫
    isoWhiskerLeft (iX ⋙ pF)
      (associator iY
          ((smallEtaleToSpaces Y).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
            (smallEtaleTopology Y) (spacesEtaleTopology Y))
          (pG ⋙ iZ) ≪≫
        isoWhiskerRight (asIso ((smallEtaleToSpaces Y).sheafAdjunctionCocontinuous
          AddCommGrpCat.{u + 1} (smallEtaleTopology Y) (spacesEtaleTopology Y)).unit).symm (pG ⋙ iZ) ≪≫
        leftUnitor (pG ⋙ iZ)) ≪≫
    isoWhiskerLeft iX
      (associator pF pG iZ ≪≫ isoWhiskerRight (spacesEtaleAbelianPushforwardComp f g) iZ) ≪≫
    (sheafPushforwardAbelianFactor (f ≫ g)).symm

/-- Inverse image of abelian small-étale sheaves along a composite is the composite inverse
image. -/
def sheafInverseImage_comp {X Y Z : AlgebraicSpace S} (p : Y ⟶ Z) (q : X ⟶ Y)
    [(smallEtaleToSpaces Y).IsCoverDense (spacesEtaleTopology Y)] :
    sheafInverseImage AddCommGrpCat.{u + 1} p ⋙
        sheafInverseImage AddCommGrpCat.{u + 1} q ≅
      sheafInverseImage AddCommGrpCat.{u + 1} (q ≫ p) :=
  leftAdjointCompIso (sheafAdjunction AddCommGrpCat.{u + 1} p) (sheafAdjunction AddCommGrpCat.{u + 1} q)
    (sheafAdjunction AddCommGrpCat.{u + 1} (q ≫ p)) (sheafPushforwardAbelian_comp q p)

section

variable {X Y X' Y' : AlgebraicSpace S}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable [(smallEtaleToSpaces Y).IsCoverDense (spacesEtaleTopology Y)]
variable [(smallEtaleToSpaces X).IsCoverDense (spacesEtaleTopology X)]

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
  rfl

/-- The underived mate `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of a cartesian square of algebraic spaces. -/
def smallEtaleAbelianBaseChange :
    sheafPushforwardAbelian f ⋙ sheafInverseImage AddCommGrpCat.{u + 1} g ⟶
      sheafInverseImage AddCommGrpCat.{u + 1} g' ⋙ sheafPushforwardAbelian f' :=
  DerivedBaseChange.map (sheafAdjunction AddCommGrpCat.{u + 1} f) (sheafAdjunction AddCommGrpCat.{u + 1} f')
    (smallEtaleAbelianInverseImageSquare f g f' g' h_cart)

/-- `smallEtaleAbelianBaseChange` is the right mate of the inverse-image square. -/
theorem smallEtaleAbelianBaseChange_eq :
    smallEtaleAbelianBaseChange f g f' g' h_cart =
      DerivedBaseChange.map (sheafAdjunction AddCommGrpCat.{u + 1} f)
        (sheafAdjunction AddCommGrpCat.{u + 1} f')
        (smallEtaleAbelianInverseImageSquare f g f' g' h_cart) :=
  rfl

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
  rfl

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

/-- The degree-`q` right derivative of the underived base-change mate between the
composite functors `f_* ⋙ g⁻¹` and `(g')⁻¹ ⋙ f'_*`, evaluated at an abelian sheaf. -/
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
  rfl

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
      (sheafPushforwardAbelian f) (sheafAdjunction AddCommGrpCat.{u + 1} f))
    (Adjunction.Derived.Plus.adjunction (smallEtaleInverseExact f')
      (sheafPushforwardAbelian f') (sheafAdjunction AddCommGrpCat.{u + 1} f'))
    (smallEtaleDerivedInverseImageSquare f g f' g' h_cart)

/-- `smallEtaleDerivedBaseChange` is the mate of `smallEtaleDerivedInverseImageSquare`. -/
theorem smallEtaleDerivedBaseChange_eq :
    smallEtaleDerivedBaseChange f g f' g' h_cart =
      DerivedBaseChange.map
        (Adjunction.Derived.Plus.adjunction (smallEtaleInverseExact f)
          (sheafPushforwardAbelian f) (sheafAdjunction AddCommGrpCat.{u + 1} f))
        (Adjunction.Derived.Plus.adjunction (smallEtaleInverseExact f')
          (sheafPushforwardAbelian f') (sheafAdjunction AddCommGrpCat.{u + 1} f'))
        (smallEtaleDerivedInverseImageSquare f g f' g' h_cart) :=
  rfl

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
  rfl

end

section

variable {X Y Y' : AlgebraicSpace S}
variable (f : X ⟶ Y) (g : Y' ⟶ Y)
variable [(smallEtaleToSpaces Y).IsCoverDense (spacesEtaleTopology Y)]
variable [(smallEtaleToSpaces X).IsCoverDense (spacesEtaleTopology X)]
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
  rfl

end

end AlgebraicGeometry.AlgebraicSpace
