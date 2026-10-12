/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialOperator
import StacksCheckRecall

/-!
# Lemma 18.34.2

Compatibility facade for the reusable composition API for differential operators on ringed
sites.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}}
variable (φ : O₁ ⟶ O₂)
variable {E F G : ringedSiteModuleCategory J O₂} {k k' : ℕ}
variable {D : (restrictionAlong φ).obj E ⟶ (restrictionAlong φ).obj F}
variable {D' : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G}
variable (hD : IsDifferentialOperatorOfOrder φ D k)
variable (hD' : IsDifferentialOperatorOfOrder φ D' k')

/- Lemma 18.34.2 (09CS): composing differential operators adds their order bounds. -/
@[stacks 09CS]
#check
  (IsDifferentialOperatorOfOrder.comp φ hD hD' :
    IsDifferentialOperatorOfOrder φ (D ≫ D') (k + k'))

end SheafOfModules.RingedSite
