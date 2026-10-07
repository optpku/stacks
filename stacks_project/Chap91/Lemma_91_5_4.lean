module

public import stacks_project.Chap91.Lemma_91_5_4_Obstruction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Obstruction to lifting a map of modules along a first-order thickening

Along a first-order thickening of ringed spaces, an `𝒪_X`-linear map
`φ : i^* ℱ' ⟶ i^* 𝒢'` lifts to an `𝒪_{X'}`-linear map `ℱ' ⟶ 𝒢'` if and only if
the canonical class `obstruction φ` in `Ext⁽1⁾(L(i)^* ℱ', ℐ𝒢')` vanishes.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Hom.ModuleMap
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback
  RingedSpaceDerivedPushforward

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom
namespace ModuleMap

variable {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]
variable [(Hom.pullback i).Additive] [(Hom.pushforward i).Additive]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [RingedSite.Hom.DerivedAdjunction.HasPair (opensRingedSiteHom i)]
variable [(moduleDerivedPushforward i).CommShift ℤ]

/-- Lemma 91.5.4 Let `i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'})` be a first-order thickening of
ringed spaces. Let `ℱ'`, `𝒢'` be `𝒪_{X'}`-modules and set `ℱ = i^* ℱ'` and
`𝒢 = i^* 𝒢'`. Let `φ : ℱ ⟶ 𝒢` be an `𝒪_X`-linear map. There is a canonical class
`obstruction φ` in `Ext⁽1⁾(L(i)^* ℱ', ℐ𝒢')` whose vanishing is necessary and
sufficient for the existence of a lift of `φ` to an `𝒪_{X'}`-linear map
`φ' : ℱ' ⟶ 𝒢'`. -/
@[stacks 08LK]
theorem obstruction_eq_zero_iff {F' G' : X'.Modules}
    (φ : (i^*).obj F' ⟶ (i^*).obj G') :
    obstruction φ = 0 ↔ Nonempty (Lift F' G' φ) := sorry

end ModuleMap
end AlgebraicGeometry.RingedSpace.Hom
