/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived.Composition.Basic

/-!
# Algebra-Tensor Comparisons for Composed Derived Tensor Functors

This leaf specializes the general composition comparison to the canonical algebra-tensor
bimodules and the literal ground-ring triple tensor.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace DifferentialGradedBimodule.Tensor.Derived

variable {R : Type u} [CommRing R]

/-- Equation 22.34.1.1 (0BZ4): the canonical map from
`(A ⊗[R] B)_B ⊗_Bᴸ {}_B(B ⊗[R] C)_C` to the literal ground-ring triple tensor
`A ⊗[R] (B ⊗[R] C)`. -/
@[stacks 0BZ4]
noncomputable def AlgebraTensor.comparison (A B C : CochainDGAlgebra.{u, v} R) :
    (derivedFunctor (algebra B C)).obj
        ((DifferentialGradedModule.Derived.Q B).obj
          (DifferentialGradedBimodule.Tensor.AlgebraTensor.rightOnK A B)) ⟶
      (DifferentialGradedModule.Derived.Q C).obj
        ⟨DifferentialGradedBimodule.Tensor.AlgebraTensor.tripleRightModule A B C⟩ :=
  ordinaryComparison (algebra A B) (algebra B C) ≫
    (DifferentialGradedModule.Derived.Q C).map
      (DifferentialGradedBimodule.Tensor.AlgebraTensor.contractionOnK A B C)

/-- The algebra-tensor comparison factors as the ordinary derived-to-underived projection
followed by contraction of the two middle algebra factors. -/
@[stacks 0BZ4 "algebra-tensor comparison factorization"]
theorem AlgebraTensor.comparison_fac (A B C : CochainDGAlgebra.{u, v} R) :
    AlgebraTensor.comparison A B C =
      ordinaryComparison (algebra A B) (algebra B C) ≫
        (DifferentialGradedModule.Derived.Q C).map
          (DifferentialGradedBimodule.Tensor.AlgebraTensor.contractionOnK A B C) := sorry

/-- Lemma 22.34.2 (0BZ5): if the algebra-tensor comparison is invertible, every pair of
composable differential graded bimodules admits a differential graded bimodule representing
the composite of their derived tensor functors. -/
@[stacks 0BZ5]
theorem AlgebraTensor.existsComposite_of_comparison
    {A B C : CochainDGAlgebra.{u, v} R}
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (h_comparison : IsIso (AlgebraTensor.comparison A B C)) :
    ∃ N'' : DifferentialGradedBimodule.{u, v, v, v} A C,
      RepresentsComposite N N' N'' := sorry

/-- Under the algebra-tensor comparison hypothesis, the explicit relative tensor bimodule itself
represents the composite derived tensor functor. -/
@[stacks 0BZ5 "explicit algebra-tensor composite represents derived composition"]
theorem AlgebraTensor.representsComposite_of_comparison
    {A B C : CochainDGAlgebra.{u, v} R}
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (h_comparison : IsIso (AlgebraTensor.comparison A B C)) :
    RepresentsComposite N N' (bimodule N N') := sorry

end DifferentialGradedBimodule.Tensor.Derived
