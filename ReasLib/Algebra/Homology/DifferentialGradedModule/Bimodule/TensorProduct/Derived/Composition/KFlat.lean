/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.KFlat
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.KFlat
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived.Composition.AlgebraTensor
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived.Composition.GroundTensor

/-!
# K-Flat Criteria for Composed Derived Tensor Functors

This leaf collects the K-flat specializations of the algebra-tensor and ground-ring comparison
APIs. The generic composition layer does not depend on K-flatness.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace DifferentialGradedBimodule.Tensor.Derived

variable {R : Type u} [CommRing R]

namespace GroundTensor

/-- K-flatness of `C` is a sufficient condition for the ordinary tensor `A ⊗[R] C` to
represent its derived tensor.  This is the DG-algebra specialization of
`DerivedCategory.DerivedTensor.Bifunctor.counitAppOfComplex_isIso_of_isKFlat_right`. -/
@[stacks 09S4 "K-flat ordinary tensor model"]
theorem representsDerived_of_isKFlat (A C : CochainDGAlgebra.{u, u} R)
    (hC : C.IsKFlat) :
    RepresentsDerived A C := sorry

end GroundTensor

/-- Lemma 22.34.3 (1) (09S4): if `C` is K-flat over `R`, the canonical map
`(A ⊗[R] B)_B ⊗_Bᴸ {}_B(B ⊗[R] C)_C ⟶
  A ⊗[R] (B ⊗[R] C)` is an isomorphism. -/
@[stacks 09S4]
theorem AlgebraTensor.comparison_isIso_of_isKFlat
    (A B C : CochainDGAlgebra.{u, v} R) (hC : C.IsKFlat) :
    IsIso (AlgebraTensor.comparison A B C) := sorry

/-- Lemma 22.34.3 (2) (09S4): if `C` is K-flat over `R`, the composite of derived
tensor functors associated to any composable bimodules is represented by some differential
graded `(A, C)`-bimodule. -/
@[stacks 09S4]
theorem existsComposite_of_isKFlat
    {A B C : CochainDGAlgebra.{u, v} R}
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) (hC : C.IsKFlat) :
    ∃ N'' : DifferentialGradedBimodule.{u, v, v, v} A C,
      RepresentsComposite N N' N'' := sorry

/-- If the target DGA is K-flat over the ground ring, the explicit relative tensor bimodule
itself represents the composite derived tensor functor. -/
@[stacks 09S4 "explicit K-flat composite represents derived composition"]
theorem representsComposite_of_isKFlat
    {A B C : CochainDGAlgebra.{u, v} R}
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) (hC : C.IsKFlat) :
    RepresentsComposite N N' (bimodule N N') := sorry

end DifferentialGradedBimodule.Tensor.Derived
