/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.Duality.Sequential
public import ReasLib.CategoryTheory.Monoidal.Closed.Exactness
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Contravariant
import Mathlib.Tactic.CrossRefAttribute

/-!
# Duality and sequential homotopy colimits

Internal Hom converts a sequential homotopy colimit into a homotopy limit whenever its
contravariant source functor is triangulated.  Stagewise dualizability then replaces the
internal-Hom tower by the canonical dual-tensor tower.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Pretriangulated.Opposite
universe u v

namespace CategoryTheory.HomotopyColimit.IsOf

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C]
variable [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Internal Hom into `E` converts a sequential homotopy colimit into the homotopy limit of
the contravariant internal-Hom inverse system. -/
@[stacks 0DJI "internal Hom of a sequential homotopy colimit"]
theorem internalHom
    {K : ℕ ⥤ C} {Khocolim : C} (hK : HomotopyColimit.IsOf K Khocolim) (E : C)
    [((MonoidalClosed.internalHom (C := C)).flip.obj E : Cᵒᵖ ⥤ C).CommShift ℤ]
    [((MonoidalClosed.internalHom (C := C)).flip.obj E : Cᵒᵖ ⥤ C).IsTriangulated] :
    HomotopyLimit.IsOf (MonoidalClosed.InternalHom.tower K E)
      ((ihom Khocolim).obj E) := sorry

/-- If every stage of a sequential diagram is right-dualizable, internal Hom out of its
homotopy colimit is the homotopy limit of the dual-tensor inverse system. -/
@[stacks 0DJI "dual-tensor homotopy-limit formula"]
theorem dualTensor
    {K : ℕ ⥤ C} {Khocolim : C} (hK : HomotopyColimit.IsOf K Khocolim)
    (hdual : ∀ n, IsRightDualizable (K.obj n)) (E : C)
    [((MonoidalClosed.internalHom (C := C)).flip.obj E : Cᵒᵖ ⥤ C).CommShift ℤ]
    [((MonoidalClosed.internalHom (C := C)).flip.obj E : Cᵒᵖ ⥤ C).IsTriangulated] :
    HomotopyLimit.IsOf (MonoidalClosed.Dual.tensorTower K E)
      ((ihom Khocolim).obj E) := sorry

end CategoryTheory.HomotopyColimit.IsOf

end
