/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FiniteFreeRetract.Duality
public import ReasLib.CategoryTheory.Monoidal.Duality.Injective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Injectivity after tensoring by locally finite-free retracts

The categorical injectivity theorem for dualizable tensor factors specializes to module sheaves
which are locally retracts of finite free modules.  This is the site-level owner; ringed spaces
inherit it through their canonical opens site.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FiniteFreeRetract.IsLocal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O : Sheaf J CommRingCat.{max u v}}
variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{max u v}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
/-- Left tensoring by a locally finite-free retract preserves injective module sheaves. -/
instance tensorLeft_preservesInjectiveObjects
    (M : ringedSiteModuleCategory J O) [FiniteFreeRetract.IsLocal M] :
    (tensorLeft M).PreservesInjectiveObjects := sorry

/-- Right tensoring by a locally finite-free retract preserves injective module sheaves. -/
instance tensorRight_preservesInjectiveObjects
    (M : ringedSiteModuleCategory J O) [FiniteFreeRetract.IsLocal M] :
    (tensorRight M).PreservesInjectiveObjects := sorry

/-- Tensoring a locally finite-free retract with an injective module sheaf gives an injective
module sheaf. -/
@[stacks 01E7 "ringed-site form"]
theorem tensor_injective
    (M I : ringedSiteModuleCategory J O) [FiniteFreeRetract.IsLocal M]
    (hI : Injective I) :
    Injective (M ⊗ I) := sorry

end SheafOfModules.RingedSite.FiniteFreeRetract.IsLocal
