/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorHom.Derived.Parametrized
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open DifferentialGradedBimodule

universe u v

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, v} R}
variable (N : DifferentialGradedBimodule A B)

/- Lemma 22.33.5 (09LT): specialize an underived adjunction `G ⊣ F` to tensoring by a DG
bimodule and its internal-Hom functor. If both pointwise derived functors are everywhere
defined, their canonical total left and right derived functors remain adjoint. -/
@[stacks 09LT] #check
  (TensorHom.derivedAdjunction N :
    Tensor.derivedFunctor N ⊣ InternalHom.derivedFunctor N)

/- The reusable generalization localizes the bimodule parameter itself.  Thus every derived
bimodule `K`, not only one presented by a chosen strict `N`, determines the pointwise
tensor-Hom adjunction. -/
variable (K : Derived.Category.{u, v} A B)

#check (TensorHom.Derived.parametrizedAdjunction A B :
  Tensor.derivedBifunctor A B ⊣₂ InternalHom.derivedBifunctor A B)
#check TensorHom.Derived.adjunction K
#check @TensorHom.Derived.homEquiv
#check @TensorHom.Derived.homLinearEquiv
#check @TensorHom.Derived.homEquiv_naturality_bimodule
#check @TensorHom.Derived.adjunction_object
#check @TensorHom.Derived.homEquiv_object_apply
#check @TensorHom.Derived.homEquiv_object_symm_apply

#synth ((Tensor.derivedBifunctor A B).obj K).IsLeftAdjoint
#synth ((InternalHom.derivedBifunctor A B).obj (op K)).IsRightAdjoint

/- The derived tensor-Hom equivalence and its bifunctoriality are reusable independently of
the adjunction structure. -/
#check @TensorHom.derivedHomEquiv
#check @TensorHom.derivedHomEquiv_naturality_left
#check @TensorHom.derivedHomEquiv_naturality_right
#check @TensorHom.derivedHomEquiv_naturality

/- The concrete adjunction carries the canonical shift-compatible triangulated structure;
downstream shift formulas use Mathlib's adjunction API directly. -/
#check @TensorHom.derivedAdjunction_commShift
#check @TensorHom.derivedAdjunction_isTriangulated
#check @CategoryTheory.Adjunction.shift_unit_app
#check @CategoryTheory.Adjunction.shift_counit_app
#check @CategoryTheory.Adjunction.derived
