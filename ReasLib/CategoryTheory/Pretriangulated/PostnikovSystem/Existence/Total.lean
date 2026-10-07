module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Existence
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Total.IsIso.Levelwise

@[expose] public section

/-!
# Isomorphism Consequences of Postnikov-System Existence

This leaf promotes a levelwise-isomorphic comparison on a fixed finite row to
an isomorphism in the total category of finite Postnikov systems.
-/

open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.PostnikovSystem.Total.Existence

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]

/-- Successor-diagonal shifted-Hom vanishing makes any two Postnikov systems on the same finite
row isomorphic in the total category. -/
@[stacks 0D83]
theorem nonemptyIso {n : ℕ} {X : ComposableArrows D n} (P P' : PostnikovSystem X)
    (h : ShiftedHom.vanishesAboveSuccessor X.intFamily X.intFamily) :
    Nonempty (PostnikovSystem.Total.mk X P ≅ PostnikovSystem.Total.mk X P') := sorry

end CategoryTheory.PostnikovSystem.Total.Existence
