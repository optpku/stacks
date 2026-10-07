module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.InverseSystem.Preorder

/-!
# Eventually Zero Preorder Inverse Systems

This leaf owns the elementary eventual-vanishing condition on transition maps of a preorder-indexed
inverse system. It is independent of images, exactness, limits, and additive structure; sequential
inverse systems are the specialization with index preorder `ℕ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe uI vI uA vA

namespace CategoryTheory.PreorderInverseSystem

variable {I : Type uI} [Preorder I]
variable {A : Type uA} [Category.{vA} A] [HasZeroMorphisms A]

namespace Transition

/-- The transition maps of a preorder-indexed inverse system are eventually zero from every
stage. -/
@[stacks 0G39]
def EventuallyZero (F : PreorderInverseSystem I A) : Prop :=
  ∀ i : I, ∃ j : I, ∃ hij : i ≤ j, F.transitionMap hij = 0

namespace EventuallyZero

/-- A finite family of eventually-zero inverse systems has one common zero transition whenever the
index preorder admits finite upper bounds. -/
theorem finiteFamily {I : Type uI} [SemilatticeSup I] {κ : Type*} [Finite κ]
    (F : κ → PreorderInverseSystem I A)
    (hF : ∀ k, EventuallyZero (F k)) (i : I) :
    ∃ j : I, ∃ hij : i ≤ j, ∀ k : κ, (F k).transitionMap hij = 0 := sorry

end EventuallyZero

end Transition

end CategoryTheory.PreorderInverseSystem
