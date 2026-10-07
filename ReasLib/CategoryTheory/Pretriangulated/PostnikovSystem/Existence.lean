module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Extension
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Morphism.IsLevelwiseIso.Basic
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Existence and Isomorphism of Finite Postnikov Systems

This leaf applies the integer-indexed shifted-Hom vanishing condition to build
finite Postnikov systems and to compare two systems on the same finite row.
-/

open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

namespace PostnikovSystem

namespace Existence

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]

/-- Stacks 0D83, Lemma 13.41.6: a finite complex admits a Postnikov system when its reversed
integer-indexed row has the required displaced-diagonal shifted-Hom vanishing. -/
@[stacks 0D83]
theorem nonempty
    {n : ℕ} (X : ComposableArrows D n) (hX : X.IsComplex)
    (h : ShiftedHom.vanishesAboveSuccessor X.intFamily (fun i ↦ X.intFamily (i - 1))) :
    Nonempty (PostnikovSystem X) := sorry

/-- A finite complex admits a Postnikov system when its reversed integer-indexed row has
shifted-Hom vanishing above the diagonal displaced by two. -/
@[stacks 0D83]
theorem nonempty_of_vanishesAbove
    {n : ℕ} (X : ComposableArrows D n) (hX : X.IsComplex)
    (h : ShiftedHom.vanishesAbove (2 : ℤ) X.intFamily X.intFamily) :
    Nonempty (PostnikovSystem X) := sorry

end

end Existence

end PostnikovSystem

namespace PostnikovSystem.Morphism

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]

namespace Existence

/-- Stacks 0D83, Lemma 13.41.6: successor-diagonal vanishing gives a levelwise-isomorphic
comparison between any two Postnikov systems on the same finite row. -/
@[stacks 0D83]
theorem comparison
    {n : ℕ} {X : ComposableArrows D n} (P P' : PostnikovSystem X)
    (h : ShiftedHom.vanishesAboveSuccessor X.intFamily X.intFamily) :
    ∃ ψ : PostnikovSystem.Morphism P P' (𝟙 X), ψ.IsLevelwiseIso := sorry

end Existence

end

end PostnikovSystem.Morphism

end CategoryTheory
