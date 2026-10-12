/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.FirstOrder
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.Truncation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.ZerothOrder
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.PrincipalParts.FirstOrder.Truncation

/-!
# First-order sheaf projection as truncation

The projection in the canonical first principal-parts sequence is the first transition in the
principal-parts inverse system, followed by the zeroth-order identification.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.PrincipalParts.FirstOrder

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}}

/-- Tag 0G3T: the first-principal-parts sheaf projection factors through zeroth-order
truncation. -/
@[stacks 0G3T "first-order projection"]
theorem projection_eq_truncate (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) :
    projection phi F =
      PrincipalParts.truncate phi F (Nat.zero_le 1) ≫ ZerothOrder.projection phi F := sorry

end SheafOfModules.RingedSite.PrincipalParts.FirstOrder
