module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.TFAE
public import ReasLib.LinearAlgebra.UniversallyInjective.Projective

@[expose] public section

/-!
# Projective-module criteria for rings with annihilators

@stack 05GQ
-/

universe u v

namespace LinearMap.UniversallyInjective

variable {R : Type u} [CommRing R]

/-- Lemma 15.15.4, tag `05GQ`: the annihilator property for proper finitely
generated ideals is equivalent to universal injectivity, projectivity of
cokernels, complemented finite projective submodules, and splitting of
injective maps `R → R^{⊕ n}`. -/
@[stacks 05GQ]
theorem properFGIdealAnnihilator_tfae :
    List.TFAE
      [ (∀ {I : Ideal R}, I.FG → I ≠ ⊤ → I.annihilator ≠ (⊥ : Ideal R)),
        (∀ {N : Type (max u v)} [AddCommGroup N] [Module R N] [Module.Projective R N]
            {M : Type (max u v)} [AddCommGroup M] [Module R M] [Module.Projective R M]
            (f : N →ₗ[R] M), Function.Injective f →
              LinearMap.UniversallyInjective.{u, max u v, max u v, u} f),
        (∀ {N : Type (max u v)} [AddCommGroup N] [Module R N] [Module.Finite R N]
            [Module.Projective R N]
            {M : Type (max u v)} [AddCommGroup M] [Module R M] [Module.Finite R M]
            [Module.Projective R M] (f : N →ₗ[R] M), Function.Injective f →
              Module.Finite R (M ⧸ f.range) ∧ Module.Projective R (M ⧸ f.range)),
        (∀ {M : Type (max u v)} [AddCommGroup M] [Module R M] [Module.Finite R M]
            [Module.Projective R M] (N : Submodule R M) [Module.Finite R N]
            [Module.Projective R N], IsComplemented N),
        (∀ n : ℕ, ∀ f : R →ₗ[R] (Fin n → R), Function.Injective f →
            ∃ g : (Fin n → R) →ₗ[R] R, g.comp f = LinearMap.id) ] := sorry
-- Proof strategy: prove the five-cycle with `tfae_have`.  Use
-- `iff_injective_of_projective_of_annihilator` for `(1) → (2)`; apply `(2)` to the range
-- inclusion and the universally-injective cokernel criterion for `(2) → (3)`; obtain a complement
-- from projectivity of the quotient for `(3) → (4)`; split the range of an injective
-- `R → Fin n → R` for `(4) → (5)`; and recover a nonzero annihilator from the kernel of the
-- generator map of a proper finitely generated ideal for `(5) → (1)`.  Use `ULift.moduleEquiv`
-- only to align the module universes in clauses `(4)` and `(5)`.

end LinearMap.UniversallyInjective
