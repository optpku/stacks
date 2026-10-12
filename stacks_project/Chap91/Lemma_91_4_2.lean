/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.Lemma_91_4_2_Obstruction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Obstruction to lifting a map of modules along a first-order thickening

Along a first-order thickening of ringed spaces, a pair of mixed-scalar extensions together with
endpoint maps whose infinitesimal-map square commutes admits a compatible middle map if and only
if the canonical obstruction class in `Ext¹` vanishes.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom
namespace ModuleExtension

variable {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]
variable [HasExt.{u} X.Modules]
variable (E G : ModuleExtension i)

/-- Lemma 91.4.2: Let `i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'})` be a first-order thickening of ringed
spaces. Assume given extensions `0 ⟶ 𝒦 ⟶ ℱ' ⟶ ℱ ⟶ 0` and `0 ⟶ ℒ ⟶ 𝒢' ⟶ 𝒢 ⟶ 0` as in
91.4.0.1, together with maps `φ : ℱ ⟶ 𝒢` and `ψ : 𝒦 ⟶ ℒ` making the infinitesimal-map square
of `c_{ℱ'}` and `c_{𝒢'}` commute. Then the class `o(φ, ψ) = mapObstruction E G φ ψ hcomm` in
`Ext ℱ ℒ 1` vanishes if and only if there exists a map `φ' : ℱ' ⟶ 𝒢'` compatible with `φ`
and `ψ`. -/
@[stacks 08L6]
theorem mapObstruction_eq_zero_iff
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel)
    (hcomm : infinitesimalMap_comm E G φ ψ) :
    mapObstruction E G φ ψ hcomm = 0 ↔
      ∃ φ' : E.middle ⟶ G.middle,
        E.ι ≫ φ' = (i _*).map ψ ≫ G.ι ∧
          φ' ≫ G.π = E.π ≫ (i _*).map φ := sorry

end ModuleExtension
end AlgebraicGeometry.RingedSpace.Hom
