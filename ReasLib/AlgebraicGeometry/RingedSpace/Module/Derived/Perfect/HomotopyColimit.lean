/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Duality
public import ReasLib.CategoryTheory.Monoidal.Closed.Duality.HomotopyColimit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Perfect sequential diagrams and internal Hom

This leaf specializes the categorical dual-tensor homotopy-limit formula to the canonical
derived tensor product on modules over a ringed space.  Perfectness is exposed at the geometric
boundary and converted internally to right dualizability.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}
variable [KFlat.HomotopyTensorDescends X] [KFlat.TensorDescends X]
variable [KFlat.IsLocalization X]
variable [MonoidalClosed (ModuleDerived X)]

/-- Lemma 20.51.1 (0DJI), reusable ringed-space form: internal Hom out of the homotopy colimit
of a sequential diagram of perfect derived modules is the homotopy limit of its dual-tensor
inverse system. -/
@[stacks 0DJI "perfect sequential duality"]
theorem internalHom_homotopyLimit_of_isPerfect
    (K : ℕ ⥤ ModuleDerived X) {Khocolim : ModuleDerived X}
    (hperfect : ∀ n, IsPerfect (K.obj n))
    (hK : HomotopyColimit.IsOf K Khocolim) (E : ModuleDerived X) :
    HomotopyLimit.IsOf (MonoidalClosed.Dual.tensorTower K E)
      ((ihom Khocolim).obj E) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived

end
