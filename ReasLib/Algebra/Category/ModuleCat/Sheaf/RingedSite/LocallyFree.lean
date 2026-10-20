module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FiniteLocallyFree
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Rank
import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally Free Module Sheaves on Ringed Sites

Convenience import for Mathlib local freeness together with the reusable
finite-local-freeness and constant-rank refinements.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace SheafOfModules.IsLocallyFree

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- In ringed-site generality, every locally free module sheaf is quasicoherent.
This named theorem exposes Mathlib's canonical instance without requiring
downstream users to know its implementation. -/
@[stacks 01C7]
theorem isQuasicoherent (M : SheafOfModules.{w} R) [M.IsLocallyFree] :
    M.IsQuasicoherent := sorry

end SheafOfModules.IsLocallyFree
