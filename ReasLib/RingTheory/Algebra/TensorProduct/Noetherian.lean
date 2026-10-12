/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic.CrossRefAttribute

/-!
# Noetherian Algebras and Tensor Products

This leaf records reusable Noetherianity consequences of finite-type hypotheses.
The tensor-product conclusions are explicit owner theorems rather than global
instances: a tensor product can carry several algebra structures and its
orientation is part of the mathematical input, so installing these conclusions
globally would make typeclass search depend on an arbitrary presentation.

@stack 0CY6
@stack 045I
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra.FiniteType

/-- If the right factor is finite type over the base and the left factor is
Noetherian, then their tensor product is Noetherian. -/
@[stacks 0CY6 "finite-type tensor base change"]
theorem isNoetherianRing_tensor_right
    {R : Type u} {Q : Type v} {T : Type w}
    [CommRing R] [CommRing Q] [CommRing T]
    [Algebra R Q] [Algebra R T] [Algebra.FiniteType R T]
    [IsNoetherianRing Q] : IsNoetherianRing (Q ⊗[R] T) := sorry

/-- If the left tensor factor is finite type over the base and the right tensor
factor is Noetherian, then the tensor product is Noetherian. -/
@[stacks 0CY6]
theorem isNoetherianRing_tensor_left
    {R : Type u} {Q : Type v} {T : Type w}
    [CommRing R] [CommRing Q] [CommRing T]
    [Algebra R Q] [Algebra R T] [Algebra.FiniteType R T]
    [IsNoetherianRing Q] : IsNoetherianRing (T ⊗[R] Q) := sorry

end Algebra.FiniteType

namespace Algebra.EssFiniteType

/-- Tensoring a Noetherian algebra on the right with an essentially finite type
algebra on the left yields a Noetherian ring. -/
@[stacks 045I "essentially finite-type tensor base change"]
theorem isNoetherianRing_tensor_right
    {R : Type u} {Q : Type v} {T : Type w}
    [CommRing R] [CommRing Q] [CommRing T]
    [Algebra R Q] [Algebra R T] [Algebra.EssFiniteType R Q] [IsNoetherianRing T] :
    IsNoetherianRing (Q ⊗[R] T) := sorry

/-- Tensoring a Noetherian algebra with an essentially finite type field
extension preserves Noetherianity. -/
@[stacks 045I]
theorem isNoetherianRing_tensor_of_fieldExtension
    {k : Type u} {K : Type v} {A : Type w}
    [Field k] [Field K] [Algebra k K] [Algebra.EssFiniteType k K]
    [CommRing A] [Algebra k A] [IsNoetherianRing A] :
    IsNoetherianRing (K ⊗[k] A) := sorry

end Algebra.EssFiniteType
