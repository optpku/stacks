module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite presentation in exact sequences

This leaf owns the exact-sequence closure properties of finitely presented
modules.
-/

@[expose] public section

universe u v w x

namespace Module

section

variable {R : Type u} [Ring R]
variable {M1 : Type v} [AddCommGroup M1] [Module R M1]
variable {M2 : Type w} [AddCommGroup M2] [Module R M2]
variable {M3 : Type x} [AddCommGroup M3] [Module R M3]

/-- In a short exact sequence of modules, finite presentation of the outer terms implies finite
presentation of the middle term. -/
@[stacks 0519 "finite presentation and exact sequences"]
theorem finitePresentation_of_exact
    (f : M1 →ₗ[R] M2) (g : M2 →ₗ[R] M3)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    [Module.FinitePresentation R M1] [Module.FinitePresentation R M3] :
    Module.FinitePresentation R M2 := sorry

/-- In a right-exact sequence, a finitely presented middle term and a finite kernel source imply
finite presentation of the quotient. -/
@[stacks 0519 "finite presentation and exact sequences"]
theorem finitePresentation_of_surjective_of_exact
    (f : M1 →ₗ[R] M2) (g : M2 →ₗ[R] M3)
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    [Module.FinitePresentation R M2] [Module.Finite R M1] :
    Module.FinitePresentation R M3 := sorry

end

namespace Finite

section

variable (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M]

/-- An `R`-module is finite exactly when it is the target of a
surjective map from a finite free module. -/
@[stacks 0518 "finite modules"]
theorem iff_exists_surjective_free :
    Module.Finite R M ↔ ∃ n : ℕ, ∃ f : (Fin n → R) →ₗ[R] M, Function.Surjective f := sorry

end

section

variable {R : Type u} [Ring R]
variable {M1 : Type v} [AddCommGroup M1] [Module R M1]
variable {M2 : Type w} [AddCommGroup M2] [Module R M2]
variable {M3 : Type x} [AddCommGroup M3] [Module R M3]

/-- In a short exact sequence, a finitely presented quotient and a finite middle term imply that
the kernel source is finite. -/
@[stacks 0519 "finite presentation and exact sequences"]
theorem of_exact_of_finitePresentation
    (f : M1 →ₗ[R] M2) (g : M2 →ₗ[R] M3)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    [Module.FinitePresentation R M3] [Module.Finite R M2] :
    Module.Finite R M1 := sorry

end

end Finite

namespace FinitePresentation

section

variable (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]

/-- An `R`-module is finitely presented exactly when it admits a
finite free presentation. -/
@[stacks 0518 "finitely presented modules"]
theorem iff_exists_exact_free_sequence :
    Module.FinitePresentation R M ↔
      ∃ n m : ℕ, ∃ f : (Fin m → R) →ₗ[R] (Fin n → R),
        ∃ g : (Fin n → R) →ₗ[R] M, Function.Exact f g ∧ Function.Surjective g := sorry

end

end FinitePresentation
end Module
