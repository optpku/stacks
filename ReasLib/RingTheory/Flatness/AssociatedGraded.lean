/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Tensor

/-!
# Flatness from associated graded pieces

@stack 0AS8

This leaf states the flatness criteria whose hypotheses use the canonical
tensor maps to the associated graded pieces of a filtered module.
-/

@[expose] public section

universe u v

namespace Module.Flat.AssociatedGraded

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Lemma 10.99.9 (1) (Stacks `0AS8`): flatness modulo `I`, together with
injectivity of the canonical map to the degree-one associated graded piece,
implies flatness modulo `I ^ 2`. -/
@[stacks 0AS8 "(1), flatness modulo the square"]
theorem modIdealSq_of_tensorToPiece_injective
    {I : Ideal R}
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (hinj : Function.Injective (Ideal.AssociatedGraded.tensorToPiece I M 1)) :
    Module.Flat (R ⧸ I ^ 2) (M ⧸ (I ^ 2 • (⊤ : Submodule R M))) := sorry

/-- Lemma 10.99.9 (2) (Stacks `0AS8`): if the canonical maps to the associated
graded pieces through degree `k` are injective, flatness modulo `I` lifts to
flatness modulo `I ^ (k + 1)`. -/
@[stacks 0AS8 "(2), flatness modulo an ideal power"]
theorem modIdealPowSucc_of_tensorToPiece_injective
    {I : Ideal R} (k : ℕ)
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (hinj : ∀ n : ℕ, 1 ≤ n → n ≤ k →
      Function.Injective (Ideal.AssociatedGraded.tensorToPiece I M n)) :
    Module.Flat (R ⧸ I ^ (k + 1))
      (M ⧸ (I ^ (k + 1) • (⊤ : Submodule R M))) := sorry

end Module.Flat.AssociatedGraded
