/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Definition_92_22_1_Cotangent
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Degree-zero homology of the sheaf cotangent complex

The cochain augmentation `L(φ) ⟶ Ω(φ)[0]` is the sheaf-level analogue of the ring-level
comparison of Lemma 92.4.5: its degree-zero component is Kähler base change along the
standard-resolution augmentation, and the induced map on `H^0` identifies `L(φ).homology 0`
with `Ω(φ)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open Opposite
open AlgebraicTopology
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite.CotangentComplex
open scoped Simplicial

noncomputable section

universe u

namespace SheafOfModules.RingedSite.CotangentComplex

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]

/-- The standard-resolution augmentation `P_n ⟶ B` is a morphism of objects of `Under A`. -/
theorem standardAugmentation_w (A : Sheaf J CommRingCat.{u}) (B : Under A)
    (n : SimplexCategoryᵒᵖ) :
    𝟙 A ≫ B.hom = (standardTerm A B n).hom ≫ standardAugmentation A B n :=
  sorry

/-- The Kähler base-change map `Ω_{P_0/A} ⊗_{P_0} B ⟶ Ω(φ)` along the standard-resolution
augmentation. -/
def standardToKaehler {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    (simplicialModule A (Under.mk φ)).obj (op ⦋0⦌) ⟶ Ω(φ) :=
  ((extendRestrictAdj
      (standardAugmentation A (Under.mk φ) (op ⦋0⦌))).homEquiv _ _).symm
    (RelativeDifferentials.map
      ⟨standardAugmentation_w A (Under.mk φ) (op ⦋0⦌)⟩)

/-- The degree-zero component of the canonical cochain comparison `L(φ) ⟶ Ω(φ)[0]`, obtained by
transporting Kähler base change of the standard-resolution augmentation along `objXIso`. -/
def toKaehler {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    L(φ).X 0 ⟶ Ω(φ) :=
  (objXIso A (Under.mk φ) 0).hom ≫ standardToKaehler φ

/-- The outgoing differential of `L(φ)` into degree zero followed by `toKaehler` is zero. -/
theorem d_comp_toKaehler {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (i : ℤ) (h : (ComplexShape.up ℤ).Rel i 0) :
    L(φ).d i 0 ≫ toKaehler φ = 0 :=
  sorry

/-- The canonical cochain comparison `L(φ) ⟶ Ω(φ)[0]`. -/
def augmentation {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    L(φ) ⟶ (single (SheafOfModules (ringSheaf J B)) (ComplexShape.up ℤ) 0).obj Ω(φ) :=
  mkHomToSingle (toKaehler φ) (d_comp_toKaehler φ)

/-- The degree-zero component of `augmentation` is `toKaehler` followed by the inverse of
`singleObjXSelf`. -/
theorem augmentation_f_zero {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    (augmentation φ).f 0 =
      toKaehler φ ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 (Ω(φ))).inv :=
  sorry

/-- The canonical map `H^0(L(φ)) ⟶ Ω(φ)` induced by `augmentation`. -/
def homologyZeroMap {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    L(φ).homology 0 ⟶ Ω(φ) :=
  homologyMap (augmentation φ) 0 ≫
    (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (Ω(φ))).hom

/-- The canonical map `H^0(L(φ)) ⟶ Ω(φ)` is an isomorphism. -/
instance homologyZeroMap_isIso {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    IsIso (homologyZeroMap φ) :=
  sorry

/-- The canonical identification `H^0(L(φ)) ≅ Ω(φ)` of sheaves of `B`-modules. -/
def homologyZeroIso {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    L(φ).homology 0 ≅ Ω(φ) :=
  asIso (homologyZeroMap φ)

/-- The forward morphism of `homologyZeroIso` is `homologyZeroMap`. -/
theorem homologyZeroIso_hom {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    (homologyZeroIso φ).hom = homologyZeroMap φ :=
  sorry

/-- The inverse morphism of `homologyZeroIso` is the inverse of `homologyZeroMap`. -/
theorem homologyZeroIso_inv {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    (homologyZeroIso φ).inv = inv (homologyZeroMap φ) :=
  sorry

end SheafOfModules.RingedSite.CotangentComplex
