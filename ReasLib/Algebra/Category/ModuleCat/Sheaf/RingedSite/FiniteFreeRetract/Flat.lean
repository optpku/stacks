/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FiniteFreeRetract
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat finitely presented module sheaves

This leaf owns the local finite-free retract criterion for flat finitely presented modules on a
commutative ringed site.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C,
  (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{max u v}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
/-- A flat finitely presented module sheaf is locally a retract of a finite free module
sheaf. -/
@[stacks 08FD, stacks 08BL "ringed-site form"]
theorem FiniteFreeRetract.IsLocal.ofIsFinitePresentationOfFlat
    (M : ringedSiteModuleCategory J 𝒪)
    [M.IsFinitePresentation] [IsFlat 𝒪 M] :
    FiniteFreeRetract.IsLocal M := sorry

namespace FiniteFreeRetract.IsLocal

/-- A module sheaf locally realized as a retract of a finite free module sheaf is finitely
presented. -/
@[stacks 08BL "converse, finite presentation", instance]
theorem isFinitePresentation
    (M : ringedSiteModuleCategory J 𝒪) [FiniteFreeRetract.IsLocal M] :
    M.IsFinitePresentation := sorry

/-- A module sheaf locally realized as a retract of a finite free module sheaf is flat. -/
@[stacks 08BL "converse, flatness", instance]
theorem isFlat
    (M : ringedSiteModuleCategory J 𝒪) [FiniteFreeRetract.IsLocal M] :
    IsFlat 𝒪 M := sorry

end FiniteFreeRetract.IsLocal

/-- Being locally a retract of a finite free module sheaf is equivalent to being finitely
presented and flat. -/
@[stacks 08BL "ringed-site characterization"]
theorem FiniteFreeRetract.isLocal_iff_finitePresentation_and_flat
    (M : ringedSiteModuleCategory J 𝒪) :
    FiniteFreeRetract.IsLocal M ↔ M.IsFinitePresentation ∧ IsFlat 𝒪 M := sorry

end SheafOfModules.RingedSite
