module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Total.Forget
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Functor.Basic

/-!
# Forgetful Coherence for Finite Restrictions of Postnikov Towers

This leaf identifies the underlying row of the finite total Postnikov-system
restriction with finite-row restriction.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Tower

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ k : ℤ, Functor.Additive (shiftFunctor D k)] [Pretriangulated D]

/-- Forgetting the finite Postnikov system from `finiteFunctor` recovers `rowFunctor`. -/
@[stacks 0D8Z "underlying finite row of finite-system restriction"]
theorem finiteFunctor_comp_forget (n : ℕ) :
    finiteFunctor D n ⋙ PostnikovSystem.Total.forget D n =
      rowFunctor D n := sorry

end CategoryTheory.PostnikovSystem.Tower
