/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Properties
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Rank.Invertible
import Mathlib.Tactic.CrossRefAttribute

/-!
# Invertibility of top exterior powers

The top exterior power of a finite locally free module sheaf of fixed rank is rank one, hence
tensor-invertible.  This leaf keeps that derived instance separate from the basic exterior-power
property API.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.ExteriorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- The top exterior power of a finite locally free module sheaf of rank `r` is
tensor-invertible. -/
@[stacks 0FJN "top exterior power", instance]
theorem top_isInvertible
    (F : ringedSiteModuleCategory J 𝒪) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r F] :
    isInvertibleObject (sheaf 𝒪 F r) := sorry

end SheafOfModules.RingedSite.ExteriorPower
