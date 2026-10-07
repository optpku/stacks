module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import stacks_project.Chap91.Lemma_91_5_1_IdealMul
public import stacks_project.Chap91.Lemma_91_5_1_Lift

/-!
# Canonical Ext¹ obstruction of a map of modules along a first-order thickening

An `𝒪_X`-linear map `φ : i^* ℱ' ⟶ i^* 𝒢'` determines a connecting class in
`Ext⁽1⁾(ℱ'[0], (i_* ℐ𝒢'_X)[0])` on `D(𝒪_{X'})`, and hence a canonical class
`o(φ)` in `Ext⁽1⁾(L(i)^* ℱ'[0], ℐ𝒢'_X[0])` via `i_* = R(i)_*` and the derived
adjunction `L(i)^* ⊣ R(i)_*`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open AlgebraicGeometry.RingedSpace.Hom
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback
  RingedSpaceDerivedPushforward

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom
namespace ModuleMap

variable {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]

/-- The adjunct of an `𝒪_X`-linear map `φ : i^* ℱ' ⟶ i^* 𝒢'`, as a morphism
`ℱ' ⟶ i_* i^* 𝒢'` of `𝒪_{X'}`-modules. -/
def adjunct {F' G' : X'.Modules} (φ : (i^*).obj F' ⟶ (i^*).obj G') :
    F' ⟶ (i _*).obj ((i^*).obj G') :=
  (pullbackPushforwardAdjunction i).homEquiv F' ((i^*).obj G') φ

/-- The connecting morphism of the canonical short exact sequence
`0 ⟶ i_* ℐ𝒢'_X ⟶ 𝒢' ⟶ i_* i^* 𝒢' ⟶ 0` in `D(𝒪_{X'})`. -/
def connecting (G' : X'.Modules) :
    (DerivedCategory.singleFunctor X'.Modules 0).obj ((i _*).obj ((i^*).obj G')) ⟶
      ((DerivedCategory.singleFunctor X'.Modules 0).obj
        ((i _*).obj (idealMulRestrict i G')))⟦(1 : ℤ)⟧ :=
  (ModuleExtension.ofPullback i G').shortExact.singleδ

/-- The connecting class of `φ` in `Ext⁽1⁾(ℱ'[0], (i_* ℐ𝒢'_X)[0])`. -/
def obstructionOver {F' G' : X'.Modules} (φ : (i^*).obj F' ⟶ (i^*).obj G') :
    Ext⁽(1 : ℤ)⁾((DerivedCategory.singleFunctor X'.Modules 0).obj F',
      (DerivedCategory.singleFunctor X'.Modules 0).obj
        ((i _*).obj (idealMulRestrict i G'))) :=
  (DerivedCategory.singleFunctor X'.Modules 0).map (adjunct φ) ≫ connecting G'

/-- The connecting class `obstructionOver φ` vanishes if and only if `φ` lifts to an
`𝒪_{X'}`-linear map `ℱ' ⟶ 𝒢'`. -/
theorem obstructionOver_eq_zero_iff {F' G' : X'.Modules}
    (φ : (i^*).obj F' ⟶ (i^*).obj G') :
    obstructionOver φ = 0 ↔ Nonempty (Lift F' G' φ) := sorry

variable [(Hom.pullback i).Additive] [(Hom.pushforward i).Additive]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [RingedSite.Hom.DerivedAdjunction.HasPair (opensRingedSiteHom i)]
variable [(moduleDerivedPushforward i).CommShift ℤ]

/-- The degree-one shift comparison `(R(i)_* K)⟦1⟧ ⟶ R(i)_* (K⟦1⟧)`. -/
def comparisonShift (K : DerivedCategory X.Modules) :
    ((R(i)_*).obj K)⟦(1 : ℤ)⟧ ⟶ (R(i)_*).obj (K⟦(1 : ℤ)⟧) :=
  ((R(i)_*).commShiftIso (1 : ℤ)).inv.app K

/-- The canonical obstruction class `o(φ)` in `Ext⁽1⁾(L(i)^* ℱ'[0], ℐ𝒢'_X[0])`. -/
def obstruction {F' G' : X'.Modules} (φ : (i^*).obj F' ⟶ (i^*).obj G') :
    Ext⁽(1 : ℤ)⁾((L(i)^*).obj ((DerivedCategory.singleFunctor X'.Modules 0).obj F'),
      (DerivedCategory.singleFunctor X.Modules 0).obj (idealMulRestrict i G')) :=
  ((modulePullbackDerivedPushforwardAdjunction i).homEquiv _ _).symm
    (obstructionOver φ ≫
      (moduleDerivedPushforward.comparison i ((i _*).obj (idealMulRestrict i G'))
          (idealMulRestrict i G') (𝟙 _))⟦(1 : ℤ)⟧' ≫
        comparisonShift
          ((DerivedCategory.singleFunctor X.Modules 0).obj (idealMulRestrict i G')))

/-- `obstruction φ` is the adjunct of the connecting class after the derived pushforward
comparison and the degree-one shift comparison. -/
theorem obstruction_eq {F' G' : X'.Modules} (φ : (i^*).obj F' ⟶ (i^*).obj G') :
    obstruction φ =
      ((modulePullbackDerivedPushforwardAdjunction i).homEquiv _ _).symm
        (obstructionOver φ ≫
          (moduleDerivedPushforward.comparison i ((i _*).obj (idealMulRestrict i G'))
              (idealMulRestrict i G') (𝟙 _))⟦(1 : ℤ)⟧' ≫
            comparisonShift
              ((DerivedCategory.singleFunctor X.Modules 0).obj
                (idealMulRestrict i G'))) := sorry

end ModuleMap
end AlgebraicGeometry.RingedSpace.Hom
