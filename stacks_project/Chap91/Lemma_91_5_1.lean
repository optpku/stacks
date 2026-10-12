/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.Lemma_91_5_1_IdealMul
public import stacks_project.Chap91.Lemma_91_5_1_Lift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lifts of maps of modules along a first-order thickening of ringed spaces

Along a first-order thickening, the type of `𝒪_{X'}`-linear lifts of an `𝒪_X`-linear map
`φ : i^* ℱ' ⟶ i^* 𝒢'` is, if nonempty, a principal homogeneous space under
`Hom_{𝒪_X}(ℱ, ℐ𝒢')`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Hom.ModuleMap
open AlgebraicGeometry.RingedSpace.Hom.ModuleMap.Lift
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom
namespace ModuleMap

variable {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]
variable {F' G' : X'.Modules} {φ : (i^*).obj F' ⟶ (i^*).obj G'}

/-- Lemma 91.5.1 Let `i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'})` be a first-order thickening of ringed
spaces. Let `ℱ'`, `𝒢'` be `𝒪_{X'}`-modules. Set `ℱ = i^* ℱ'` and `𝒢 = i^* 𝒢'`. Let
`φ : ℱ ⟶ 𝒢` be an `𝒪_X`-linear map. The set of lifts of `φ` to an `𝒪_{X'}`-linear map
`φ' : ℱ' ⟶ 𝒢'` is, if nonempty, a principal homogeneous space under
`Hom_{𝒪_X}(ℱ, ℐ𝒢')`. -/
@[stacks 08LH]
theorem lift_principalHomogeneous (φ' φ'' : Lift F' G' φ) :
    ∃! α : (i^*).obj F' ⟶ idealMulRestrict i G', perturb α φ' = φ'' := sorry

end ModuleMap
end AlgebraicGeometry.RingedSpace.Hom
