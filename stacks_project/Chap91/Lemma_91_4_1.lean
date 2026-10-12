/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CommSq
public import stacks_project.Chap91.Lemma_91_4_1_Compatible
import Mathlib.Tactic.CrossRefAttribute

/-!
# Compatible maps of mixed-scalar extensions along a first-order thickening

Along a first-order thickening, a compatible `𝒪_{X'}`-linear map of 08L4 extensions makes the
restricted infinitesimal-map square commute, and the fiber of such maps is a principal
homogeneous space under `Hom_{𝒪_X}(ℱ, ℒ)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom
namespace ModuleExtension

open CompatibleMap

variable {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]
variable (E E' : ModuleExtension i)

/-- Lemma 91.4.1 (1) Let `i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'})` be a first-order thickening of ringed
spaces. Given mixed-scalar extensions `0 ⟶ 𝒦 ⟶ ℱ' ⟶ ℱ ⟶ 0` and `0 ⟶ ℒ ⟶ 𝒢' ⟶ 𝒢 ⟶ 0` as in
91.4.0.1 and maps `φ : ℱ ⟶ 𝒢` and `ψ : 𝒦 ⟶ ℒ`, any `𝒪_{X'}`-linear `φ' : ℱ' ⟶ 𝒢'` compatible
with `φ` and `ψ` makes the square `ℐ ⊗ φ` / `c_{ℱ'}` / `c_{𝒢'}` / `ψ` commute. -/
@[stacks 08L5]
theorem infinitesimalMap_commSq
    (ψ : E.kernel ⟶ E'.kernel) (φ : E.cokernel ⟶ E'.cokernel)
    (φ' : CompatibleMap E E' ψ φ) :
    CommSq E.infinitesimalMap_restrict (tensorHom (𝟙 (idealModule i)) φ) ψ
      E'.infinitesimalMap_restrict := sorry

/-- Lemma 91.4.1 (2) Let `i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'})` be a first-order thickening of ringed
spaces. Given mixed-scalar extensions as in 91.4.0.1 and maps `φ : ℱ ⟶ 𝒢` and `ψ : 𝒦 ⟶ ℒ`,
the set of `𝒪_{X'}`-linear maps `φ' : ℱ' ⟶ 𝒢'` compatible with `φ` and `ψ` is, if nonempty, a
principal homogeneous space under `Hom_{𝒪_X}(ℱ, ℒ)`. -/
@[stacks 08L5]
theorem compatibleMap_principalHomogeneous
    (ψ : E.kernel ⟶ E'.kernel) (φ : E.cokernel ⟶ E'.cokernel)
    (φ' φ'' : CompatibleMap E E' ψ φ) :
    ∃! α : E.cokernel ⟶ E'.kernel, perturb α φ' = φ'' := sorry

end ModuleExtension
end AlgebraicGeometry.RingedSpace.Hom
