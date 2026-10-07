module

public import stacks_project.Chap91.Lemma_91_5_1_IdealMul

/-!
# Lifts of an `𝒪_X`-linear map along a first-order thickening

An `𝒪_{X'}`-linear lift of `φ : i^* ℱ' ⟶ i^* 𝒢'` is a map `φ' : ℱ' ⟶ 𝒢'` whose inverse
image is `φ`. Along a first-order thickening, `Hom_{𝒪_X}(ℱ, ℐ𝒢')` acts by adding the
corresponding map into `ℐ𝒢'`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open AlgebraicGeometry.RingedSpace.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom

variable {X X' : RingedSpace.{u}} {i : X ⟶ X'}

namespace ModuleMap

/-- An `𝒪_{X'}`-linear lift of an `𝒪_X`-linear map `φ : i^* ℱ' ⟶ i^* 𝒢'`. -/
structure Lift (F' G' : X'.Modules) (φ : (i^*).obj F' ⟶ (i^*).obj G') where
  /-- The underlying `𝒪_{X'}`-module morphism `ℱ' ⟶ 𝒢'`. -/
  hom : F' ⟶ G'
  /-- Inverse image along `i` recovers `φ`. -/
  restrict : (i^*).map hom = φ

namespace Lift

variable {F' G' : X'.Modules} {φ : (i^*).obj F' ⟶ (i^*).obj G'}

/-- Assemble a lift of `φ` from an `𝒪_{X'}`-module map whose inverse image is `φ`. -/
def of (hom : F' ⟶ G') (restrict : (i^*).map hom = φ) : Lift F' G' φ where
  hom := hom
  restrict := restrict

/-- A lift of `φ` makes the pullback-pushforward unit square commute. -/
theorem spec (φ' : Lift F' G' φ) :
    φ'.hom ≫ (pullbackPushforwardAdjunction i).unit.app G' =
      (pullbackPushforwardAdjunction i).unit.app F' ≫ (i _*).map φ := sorry

/-- A middle map underlies a lift of `φ` if and only if the unit square with `φ` commutes. -/
theorem spec_iff [IsFirstOrderThickening i] (hom : F' ⟶ G') :
    (∃ φ' : Lift F' G' φ, φ'.hom = hom) ↔
      hom ≫ (pullbackPushforwardAdjunction i).unit.app G' =
        (pullbackPushforwardAdjunction i).unit.app F' ≫ (i _*).map φ := sorry

variable [IsFirstOrderThickening i]

/-- The difference of two lifts of `φ` is killed by the pullback-pushforward unit of `𝒢'`. -/
theorem hom_sub_comp_unit (φ' φ'' : Lift F' G' φ) :
    (φ''.hom - φ'.hom) ≫ (pullbackPushforwardAdjunction i).unit.app G' = 0 := sorry

/-- Translate a lift of `φ` by an `𝒪_X`-linear map `α : ℱ ⟶ ℐ𝒢'`. -/
def perturb (α : (i^*).obj F' ⟶ idealMulRestrict i G') (φ' : Lift F' G' φ) :
    Lift F' G' φ where
  hom := φ'.hom + homIdealMulEquiv i F' G' α ≫ idealMulι i G'
  restrict := sorry

/-- The unique `𝒪_X`-linear map `ℱ ⟶ ℐ𝒢'` measuring the difference of two lifts of `φ`. -/
def difference (φ' φ'' : Lift F' G' φ) :
    (i^*).obj F' ⟶ idealMulRestrict i G' :=
  (homIdealMulEquiv i F' G').symm
    (kernel.lift ((pullbackPushforwardAdjunction i).unit.app G')
      (φ''.hom - φ'.hom) (hom_sub_comp_unit φ' φ''))

/-- Relative to one lift of `φ`, perturbation by `Hom_{𝒪_X}(ℱ, ℐ𝒢')` parametrizes all lifts. -/
def perturbEquiv (φ' : Lift F' G' φ) :
    ((i^*).obj F' ⟶ idealMulRestrict i G') ≃ Lift F' G' φ where
  toFun α := perturb α φ'
  invFun φ'' := difference φ' φ''
  left_inv := sorry
  right_inv := sorry

/-- The underlying middle map of a `Hom_{𝒪_X}(ℱ, ℐ𝒢')`-translate. -/
theorem perturb_hom (α : (i^*).obj F' ⟶ idealMulRestrict i G') (φ' : Lift F' G' φ) :
    (perturb α φ').hom = φ'.hom + homIdealMulEquiv i F' G' α ≫ idealMulι i G' := sorry

/-- The induced map `ℐℱ' ⟶ ℐ𝒢'` on kernels of the pullback-pushforward units. -/
def kernelMap (φ' : Lift F' G' φ) : idealMul i F' ⟶ idealMul i G' :=
  kernel.map ((pullbackPushforwardAdjunction i).unit.app F')
    ((pullbackPushforwardAdjunction i).unit.app G') φ'.hom ((i _*).map φ) (spec φ').symm

/-- Inverse image of `kernelMap` is the `𝒪_X`-linear comparison `ℐℱ'_X ⟶ ℐ𝒢'_X`. -/
def kernelMapRestrict (φ' : Lift F' G' φ) :
    idealMulRestrict i F' ⟶ idealMulRestrict i G' :=
  (i^*).map (kernelMap φ')

end Lift

end ModuleMap

end AlgebraicGeometry.RingedSpace.Hom
