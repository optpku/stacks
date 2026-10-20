module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.RepresentedHom.Tower
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Additivity of represented Hom towers

This leaf records additivity in the target morphism for represented Hom towers and their shifted
counterparts. It can be imported without the presentation, derived-limit, or short-complex layers.
@stack 0CQX
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.HomotopyColimit.RepresentedHom

variable {D : Type u} [Category.{v} D] [Preadditive D]

/-- The represented Hom tower map preserves addition in the target morphism. -/
@[simp, stacks 0CQX]
theorem towerMap_add (K : ℕ ⥤ D) {L M : D} (f g : L ⟶ M) :
    towerMap K (f + g) = towerMap K f + towerMap K g := sorry

/-- The represented Hom tower is additive as a functor of its target. -/
@[stacks 0CQX]
instance towerFunctorAdditive (K : ℕ ⥤ D) : (towerFunctor K).Additive := sorry

section Shift

variable [HasShift D ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor D n)]

/-- The shifted represented Hom tower map preserves addition in the unshifted target
morphism. -/
@[simp, stacks 0CQX]
theorem shiftedTowerMap_add (K : ℕ ⥤ D) {L M : D} (f g : L ⟶ M) :
    shiftedTowerMap K (f + g) = shiftedTowerMap K f + shiftedTowerMap K g := sorry

/-- The shifted represented Hom tower is additive as a functor of its unshifted target. -/
@[stacks 0CQX]
instance shiftedTowerFunctorAdditive (K : ℕ ⥤ D) :
    (shiftedTowerFunctor K).Additive := sorry

end Shift

end CategoryTheory.HomotopyColimit.RepresentedHom

end
