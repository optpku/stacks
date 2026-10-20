/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite presentation and tensor products

Tensor products of finitely presented modules over a commutative ring are
finitely presented. The closure property is available as an instance.
-/

@[expose] public section

open scoped TensorProduct
open TensorProduct

universe u v w

namespace Module.FinitePresentation

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Tensoring a finitely presented module with a finite free module preserves
finite presentation. -/
private lemma tensorProduct_finite_free (n : ℕ) [Module.FinitePresentation R N] :
    Module.FinitePresentation R (N ⊗[R] (Fin n → R)) := by
  exact Module.FinitePresentation.of_equiv
    (TensorProduct.piScalarRight R R N (Fin n)).symm

/-- The tensor product of finitely presented `R`-modules is finitely presented
over `R`. -/
@[stacks 05BS "(2)"]
instance tensorProduct [Module.FinitePresentation R M]
    [Module.FinitePresentation R N] : Module.FinitePresentation R (M ⊗[R] N) := by
  have hNM : Module.FinitePresentation R (N ⊗[R] M) := by
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
    -- Local instance justification (proof-local temporary data): tensoring this finite free presentation supplies the source of the surjection.
    letI : Module.FinitePresentation R (N ⊗[R] (Fin n → R)) :=
      tensorProduct_finite_free (R := R) (N := N) n
    have hker_finite : Module.Finite R (LinearMap.ker f) := by
      exact Module.Finite.of_fg (Module.FinitePresentation.fg_ker f hf)
    have hker_fg : (LinearMap.ker (LinearMap.lTensor N f)).FG := by
      -- Local instance justification (proof-local temporary data): the finite kernel of this chosen surjection supplies Submodule.fg_range.
      letI : Module.Finite R (LinearMap.ker f) := hker_finite
      have hExact : Function.Exact ((LinearMap.ker f).subtype) f :=
        LinearMap.exact_subtype_ker_map f
      have hTensorExact : Function.Exact
          (LinearMap.lTensor N (LinearMap.ker f).subtype)
          (LinearMap.lTensor N f) :=
        lTensor_exact N hExact hf
      rw [LinearMap.exact_iff] at hTensorExact
      exact hTensorExact.symm ▸
        Submodule.fg_range (LinearMap.lTensor N (LinearMap.ker f).subtype)
    exact Module.finitePresentation_of_surjective (LinearMap.lTensor N f)
      (LinearMap.lTensor_surjective N hf) hker_fg
  exact Module.FinitePresentation.of_equiv (TensorProduct.comm R N M)

end Module.FinitePresentation
