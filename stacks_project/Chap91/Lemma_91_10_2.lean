/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.Lemma_91_10_2_Obstruction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Obstruction to lifting a map of modules on a first-order thickening of ringed topoi

On a first-order thickening of ringed topoi, a pair of mixed-scalar extensions together with
endpoint maps whose infinitesimal-map square commutes admits a compatible middle map if and only
if the canonical obstruction class in Ext¹_𝒪(ℱ, ℒ) vanishes.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Abelian (Ext)
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}} {π : 𝒪' ⟶ 𝒪}
variable [IsFirstOrderThickening π]
variable [(SheafOfModules.restrictScalars (ringSheafMap π)).IsRightAdjoint]
variable [HasExt (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)]
variable (E E' : Extension π)

/-- Lemma 91.10.2: Let i : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪') be a first-order thickening of ringed
topoi. Assume given extensions 0 ⟶ 𝒦 ⟶ ℱ' ⟶ ℱ ⟶ 0 and 0 ⟶ ℒ ⟶ 𝒢' ⟶ 𝒢 ⟶ 0 as in
91.10.0.1, together with maps φ : ℱ ⟶ 𝒢 and ψ : 𝒦 ⟶ ℒ making the infinitesimal-map square
of c_ℱ' and c_𝒢' commute. Then the class o(φ, ψ) = mapObstruction E E' φ ψ h in
Ext ℱ ℒ 1 vanishes if and only if there exists a map φ' : ℱ' ⟶ 𝒢' compatible with φ
and ψ. -/
@[stacks 08MD]
theorem mapObstruction_eq_zero_iff
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel)
    (h : infMapCommSq E E' φ ψ) :
    mapObstruction E E' φ ψ h = 0 ↔
      ∃ φ' : E.middle ⟶ E'.middle, Compatible E E' φ ψ φ' := sorry

end SheafOfModules.RingedSite.FirstOrderThickening
