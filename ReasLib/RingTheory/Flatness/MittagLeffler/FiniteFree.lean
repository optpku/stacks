module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.FiniteFree.FinitePresentation
public import ReasLib.RingTheory.Flatness.MittagLeffler.Presentation
import ReasLib.Algebra.Module.FinitePresentation.Exact
import ReasLib.LinearAlgebra.TensorProduct.Domination.Surjective

/-!
# Finite-free detection of Mittag-Leffler modules

The intrinsic finite kernel-factorization condition may be tested only on finite-free source
modules. Both criteria use mutual tensor-kernel domination as their common language.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace Module.MittagLeffler

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace FiniteFree

/-- Every map from a finite-free module to `M` mutually tensor-kernel dominates a map from the
same source to a finitely presented module. -/
@[stacks 05CP "finite-free kernel factorization"]
abbrev KernelFactorization (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] : Prop :=
  ∀ (F : ModuleCat.{max u v} R) (hF : ModuleCat.finiteFree R F)
    (f : F →ₗ[R] M),
    ∃ (Q : ModuleCat.{max u v} R) (g : F →ₗ[R] Q),
      ModuleCat.isFinitePresentation R Q ∧ g.Dominates f ∧ f.Dominates g

end FiniteFree

/-- The finitely presented source criterion is equivalent to its finite-free source
specialization. -/
@[stacks 05CP "finite-free reduction"]
theorem FiniteKernelFactorization.iff_finiteFree :
    FiniteKernelFactorization R M ↔ FiniteFree.KernelFactorization R M := sorry

namespace FiniteFree

/-- Lemma 10.88.10 (05CP): a module is Mittag-Leffler exactly when finite-free source maps admit
finite kernel factorizations. -/
@[stacks 05CP]
theorem iff_kernelFactorization :
    MittagLeffler R M ↔ KernelFactorization R M := sorry

namespace KernelFactorization

/-- A Mittag-Leffler module satisfies the finite-free kernel-factorization criterion. -/
@[stacks 05CP "forward criterion"]
theorem of_mittagLeffler (hM : MittagLeffler R M) :
    FiniteFree.KernelFactorization R M := sorry

/-- The finite-free kernel-factorization criterion implies the Mittag-Leffler property. -/
@[stacks 05CP "reverse criterion"]
theorem mittagLeffler (hM : FiniteFree.KernelFactorization R M) :
    MittagLeffler R M := sorry

end KernelFactorization

end FiniteFree

end Module.MittagLeffler
