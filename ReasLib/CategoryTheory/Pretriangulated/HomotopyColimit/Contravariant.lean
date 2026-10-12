/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Definition
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Preservation
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import Mathlib.Tactic.CrossRefAttribute

/-!
# Contravariant functors and sequential homotopy colimits

A triangulated contravariant functor which preserves countable products turns a sequential
homotopy-colimit presentation into the corresponding homotopy-limit presentation.  This is the
variance-neutral core used by internal-Hom and duality applications.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped Pretriangulated.Opposite
universe u₁ v₁ u₂ v₂

namespace CategoryTheory.HomotopyColimit.IsOf

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [Preadditive C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Passing a sequential homotopy-colimit presentation to the opposite category gives the
corresponding homotopy-limit presentation. -/
@[stacks 0DJI "opposite of a sequential homotopy colimit"]
theorem op {K : ℕ ⥤ C} {X : C} (hK : HomotopyColimit.IsOf K X) :
    HomotopyLimit.IsOf K.op (Opposite.op X) := sorry

/-- A contravariant triangulated functor preserving countable products sends a sequential
homotopy colimit to the homotopy limit of the induced inverse system. -/
@[stacks 0DJI "contravariant image of a sequential homotopy colimit"]
theorem mapOp {K : ℕ ⥤ C} {X : C} (hK : HomotopyColimit.IsOf K X)
    (F : Cᵒᵖ ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    [PreservesLimitsOfShape (Discrete ℕ) F] :
    HomotopyLimit.IsOf (K.op ⋙ F) (F.obj (Opposite.op X)) := sorry

end CategoryTheory.HomotopyColimit.IsOf

end
