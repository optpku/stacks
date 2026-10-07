module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.BaseChange
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.Truncation

/-!
# Base change and truncation of principal-parts sheaves

The base-change maps at different finite orders commute with every canonical truncation map.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.PrincipalParts.BaseChange

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat.{max u v}}
variable {a : O₁ ⟶ O₁'} {phi : O₁ ⟶ O₂}
variable {phi' : O₁' ⟶ O₂'} {b : O₂ ⟶ O₂'}
variable (sq : CommSq a phi phi' b)
variable {F : ringedSiteModuleCategory J O₂}
variable {F' : ringedSiteModuleCategory J O₂'}
variable (alpha : F ⟶ (restrictionAlong b).obj F')

/-- Base change of principal-parts sheaves commutes with truncation of the order bound. -/
@[stacks 0G3W "sheaf base change commutes with truncation"]
theorem map_truncate {k l : ℕ} (h : k ≤ l) :
    map sq alpha l ≫ (restrictionAlong b).map (PrincipalParts.truncate phi' F' h) =
      PrincipalParts.truncate phi F h ≫ map sq alpha k := sorry

end SheafOfModules.RingedSite.PrincipalParts.BaseChange
