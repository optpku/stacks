/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ConstantCompletion
import StacksCheckRecall

/-!
# Lemma 61.20.1

Derived completion on a site with constant Noetherian coefficients is the
homotopy limit of the constant ideal-power quotient tensor tower.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace RingedSite.Hom.ModuleDerived.ConstantCompletion

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable (I : Ideal Λ) (K : RingedSiteDerived J (constantRingSheaf J Λ))

/- Lemma 61.20.1 (1): the left adjoint to the inclusion
`D_comp(C, Λ) ⟶ D(C, Λ)` of Proposition 52.6.12 sends `K` to a homotopy
limit of the inverse system `n ↦ K ⊗^L underline(Λ / I^n)`. -/
@[stacks 099M] #check
  (RingedSite.Hom.ModuleDerived.ConstantCompletion.completionFunctor_isHomotopyLimit J I K :
    HomotopyLimit.IsOf (completionQuotientTower (constantIdealSheaf J I) K)
      ((RingedSite.Hom.ModuleDerived.Completion.functor (constantIdealSheaf J I)).obj K).obj)

/- Lemma 61.20.1 (2): `K` is derived complete with respect to the constant
ideal sheaf of `I` if and only if `K` is a homotopy limit of
`n ↦ K ⊗^L underline(Λ / I^n)`. -/
@[stacks 099M] #check
  (RingedSite.Hom.ModuleDerived.ConstantCompletion.isDerivedComplete_iff_isHomotopyLimit J I K :
    IsDerivedCompleteWithRespectTo.{u, u, u, u} K (constantIdealSheaf J I) ↔
      HomotopyLimit.IsOf (completionQuotientTower (constantIdealSheaf J I) K) K)

end RingedSite.Hom.ModuleDerived.ConstantCompletion
