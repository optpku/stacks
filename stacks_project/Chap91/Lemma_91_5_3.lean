/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.Lemma_91_5_3_Lift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lifts of maps of modules along a strict morphism of first-order thickenings

In Situation 91.3.1, if `𝒢'` is flat over `S'` and `(f, f')` is strict, the type of
`𝒪_{X'}`-linear lifts of an `𝒪_X`-linear map `φ : i^* ℱ' ⟶ i^* 𝒢'` is, if nonempty, a
principal homogeneous space under `Hom_{𝒪_X}(ℱ, 𝒢 ⊗_{𝒪_X} f^* 𝒥)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Hom.ModuleMap
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening
namespace Hom
namespace ModuleMap

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
variable (g : T ⟶ U) {F' G' : T.right.Modules}
variable {φ : (T.hom^*).obj F' ⟶ (T.hom^*).obj G'}

/-- Lemma 91.5.3 Let `(f, f')` be a morphism of first-order thickenings as in
Situation 91.3.1. Let `ℱ'`, `𝒢'` be `𝒪_{X'}`-modules and set `ℱ = i^* ℱ'` and
`𝒢 = i^* 𝒢'`. Let `φ : ℱ ⟶ 𝒢` be an `𝒪_X`-linear map. Assume that `𝒢'` is flat
over `S'` and that `(f, f')` is a strict morphism of thickenings. The set of
lifts of `φ` to an `𝒪_{X'}`-linear map `φ' : ℱ' ⟶ 𝒢'` is, if nonempty, a
principal homogeneous space under `Hom_{𝒪_X}(ℱ, 𝒢 ⊗_{𝒪_X} f^* 𝒥)`. -/
@[stacks 08LJ]
theorem lift_principalHomogeneous [SheafOfModules.IsFlatOver G' g.right]
    (hg : IsStrict g) (φ' φ'' : Lift F' G' φ) :
    ∃! α : (T.hom^*).obj F' ⟶
        (T.hom^*).obj G' ⊗ (g.left^*).obj (idealModule U.hom),
      relativePerturb g α φ' = φ'' := sorry

end ModuleMap
end Hom
end AlgebraicGeometry.RingedSpace.Thickening
