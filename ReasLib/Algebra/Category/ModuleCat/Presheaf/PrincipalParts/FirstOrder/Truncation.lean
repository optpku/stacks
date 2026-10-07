module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.PrincipalParts.FirstOrder
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.PrincipalParts.Truncation
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.PrincipalParts.ZerothOrder
public import ReasLib.Algebra.Module.PrincipalParts.FirstOrder.Truncation
import Mathlib.Tactic.CrossRefAttribute

/-!
# First-order presheaf projection as truncation

The projection in the first principal-parts sequence agrees with truncation to order zero and the
canonical identification of zeroth principal parts.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace PresheafOfModules.PrincipalParts.FirstOrder

variable {C : Type u} [Category.{v} C]
variable {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{max u v}}

/-- The first-principal-parts presheaf projection factors through zeroth-order truncation; this is
the presheaf bridge between the algebraic 09CL construction and its 0G3T sheaf realization. -/
@[stacks 09CL "first-order presheaf projection", stacks 0G3T "presheaf bridge"]
theorem projection_eq_truncate (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) :
    projection phi F =
      PrincipalParts.truncate phi F (Nat.zero_le 1) ≫ ZerothOrder.projection phi F := sorry

end PresheafOfModules.PrincipalParts.FirstOrder
