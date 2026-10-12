/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import ReasLib.Algebra.Category.Ring.Sheaf.LocallyRinged
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Rank-one and invertible module sheaves

For module sheaves on a ringed site, finite local freeness of rank one implies tensor
invertibility.  Under local unit dichotomy the converse holds as well.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{w}}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A finite locally free module sheaf of rank one is tensor-invertible. -/
@[stacks 0B8Q "forward", stacks 0B8M "forward, ringed-site generality"]
instance rankOne_isInvertible
    (L : ringedSiteModuleCategory J 𝒪) [IsFiniteLocallyFreeOfRank 1 L] :
    isInvertibleObject L := sorry

/-- Under local unit dichotomy, an invertible module sheaf is finite locally free of rank one. -/
@[stacks 0B8Q "converse"]
theorem rankOne_of_isInvertible
    (L : ringedSiteModuleCategory J 𝒪) [isInvertibleObject L]
    [𝒪.LocalUnitDichotomy] :
    IsFiniteLocallyFreeOfRank 1 L := sorry

/-- Under local unit dichotomy, rank one and tensor invertibility are equivalent properties of a
module sheaf. -/
theorem rankOne_iff_isInvertible
    (L : ringedSiteModuleCategory J 𝒪) [𝒪.LocalUnitDichotomy] :
    IsFiniteLocallyFreeOfRank 1 L ↔ isInvertibleObject L := sorry

end SheafOfModules.RingedSite
