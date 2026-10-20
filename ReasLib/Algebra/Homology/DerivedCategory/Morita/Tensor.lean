/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.Morita.Tilting
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived.DegreeZero
public import ReasLib.Algebra.Homology.DifferentialGradedModule.DerivedMorita.Tensor

/-!
# Derived Morita Equivalences Realized by Tensor Functors

The DG theorem is the reusable core.  Its ordinary-algebra specialization uses the canonical
degree-zero DGA models and transports the resulting tensor functor back to ordinary derived
categories.
-/

@[expose] public section

noncomputable section

universe uR uA uB

open CategoryTheory
open scoped ModuleCat.Algebra

namespace DerivedCategory.Morita

variable {R : Type uR} [CommRing R]

/-- Lemma 22.37.8 (2) (09SC): if `B` is flat over `R`, an `R`-linear triangulated equivalence
`D(A) ≃ D(B)` exists exactly when a DG bimodule between the degree-zero models realizes it by
derived tensoring. -/
@[stacks 09SC]
theorem nonempty_equivalence_iff_exists_tensor
    {A : Type uA} [Ring A] [Algebra R A]
    {B : Type uB} [Ring B] [Algebra R B] [Module.Flat R B] :
    Nonempty (RLinear.TriangulatedEquivalence R
      (DerivedCategory (ModuleCat.{max uA uB} (Aᵐᵒᵖ)))
      (DerivedCategory (ModuleCat.{max uA uB} (Bᵐᵒᵖ)))) ↔
      ∃ N : DifferentialGradedBimodule.{uR, max uA uB, uA, uB}
          (CochainDGAlgebra.ofAlgebra R A) (CochainDGAlgebra.ofAlgebra R B),
        (DifferentialGradedBimodule.Tensor.ordinaryDerivedFunctor.{uR, uA, uB,
          max uA uB, max uA uB} N).IsEquivalence := sorry

/-- Under the target flatness hypothesis, the intrinsic tilting-object criterion and the
ordinary-bimodule realization criterion for derived Morita equivalence agree. -/
@[stacks 09SC "tilting criterion for ordinary derived Morita tensor realization"]
theorem exists_tilting_iff_exists_tensor
    {A : Type uA} [Ring A] [Algebra R A]
    {B : Type uB} [Ring B] [Algebra R B] [Module.Flat R B] :
    (∃ P : DerivedCategory (ModuleCat.{max uA uB} (Bᵐᵒᵖ)), IsTiltingFor R A P) ↔
      ∃ N : DifferentialGradedBimodule.{uR, max uA uB, uA, uB}
          (CochainDGAlgebra.ofAlgebra R A) (CochainDGAlgebra.ofAlgebra R B),
        (DifferentialGradedBimodule.Tensor.ordinaryDerivedFunctor.{uR, uA, uB,
          max uA uB, max uA uB} N).IsEquivalence := sorry

end DerivedCategory.Morita
