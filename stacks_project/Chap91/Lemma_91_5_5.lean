/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.Lemma_91_5_1_Lift
public import stacks_project.Chap91.Lemma_91_5_5_Obstruction
public import stacks_project.Chap91.Situation_91_6_2_Diagram
import Mathlib.Tactic.CrossRefAttribute

/-!
# Obstruction to lifting a map of modules along a strict morphism of first-order thickenings

Along a strict morphism of first-order thickenings, an `𝒪_X`-linear map
`φ : i^* ℱ' ⟶ i^* 𝒢'` between modules flat over `S'` lifts to an `𝒪_{X'}`-linear map
`ℱ' ⟶ 𝒢'` if and only if the canonical class `obstruction g φ` in
`Ext (i^* ℱ') (f^* 𝒥 ⊗ i^* 𝒢') 1` vanishes.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open AlgebraicGeometry.RingedSpace.Hom.ModuleMap (Lift)
open AlgebraicGeometry.RingedSpace.Thickening.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening
namespace Hom

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
variable (g : T ⟶ U)
variable [HasExt.{u} T.left.Modules]

/-- Lemma 91.5.5 Let `(f, f')` be a morphism of first-order thickenings as in
Situation 91.3.1. Let `ℱ'`, `𝒢'` be `𝒪_{X'}`-modules and set `ℱ = i^* ℱ'` and
`𝒢 = i^* 𝒢'`. Let `φ : ℱ ⟶ 𝒢` be an `𝒪_X`-linear map. Assume that `ℱ'` and `𝒢'`
are flat over `S'` and that `(f, f')` is a strict morphism of thickenings. There
is a canonical class `obstruction g φ` in `Ext (i^* ℱ') (f^* 𝒥 ⊗ i^* 𝒢') 1`
(the source writes `Ext¹_{𝒪_X}(ℱ, 𝒢 ⊗ f^* 𝒥)`) whose vanishing is necessary and
sufficient for the existence of a lift of `φ` to an `𝒪_{X'}`-linear map
`φ' : ℱ' ⟶ 𝒢'`. -/
@[stacks 08LL]
theorem obstruction_eq_zero_iff {F' G' : T.right.Modules}
    [SheafOfModules.IsFlatOver F' g.right] [SheafOfModules.IsFlatOver G' g.right]
    (hg : IsStrict g) (φ : (T.hom^*).obj F' ⟶ (T.hom^*).obj G') :
    obstruction g hg φ = 0 ↔ Nonempty (Lift F' G' φ) := sorry

end Hom
end AlgebraicGeometry.RingedSpace.Thickening
