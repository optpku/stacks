module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
public import ReasLib.LinearAlgebra.TensorProduct.Domination

@[expose] public section

/-!
# Finite Tensor-Kernel Factorizations

This file owns the intrinsic finite-presentation criterion used to characterize
Mittag-Leffler modules.
-/

universe u v

namespace Module.MittagLeffler

/-- A module has finite kernel factorizations if every map to it from a finitely presented
module mutually tensor-kernel dominates a map to some finitely presented module. -/
@[stacks 059E "finite kernel factorization"]
abbrev FiniteKernelFactorization (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] : Prop :=
  ∀ (P : ModuleCat.{max u v} R) (_ : ModuleCat.isFinitePresentation R P)
    (f : P →ₗ[R] M),
    ∃ (Q : ModuleCat.{max u v} R) (g : P →ₗ[R] Q),
      ModuleCat.isFinitePresentation R Q ∧ g.Dominates f ∧ f.Dominates g

end Module.MittagLeffler
