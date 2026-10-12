/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.BaseChange
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-type algebra-map descent along direct-limit base change

This leaf records property descent for a map of algebras after base change
along a directed system over one fixed base ring.  The input system is already
a system of `A`-algebras, so neither statement requires callers to choose a
stage-dependent algebra instance.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

noncomputable section

namespace Ring.DirectLimit.Algebra.BaseChange.FiniteType

variable {A : Type u} [CommRing A]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {R : I → Type w} [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
variable (f : ∀ i j, i ≤ j → R i →ₐ[A] R j)
variable [DirectedSystem R (fun i j h ↦ (f i j h : R i →+* R j))]

local notation "R∞" => Ring.DirectLimit R (fun i j h ↦ (f i j h : R i →+* R j))

/-- Stacks tag `07RG`: finiteness of the base change of a finite-type
algebra map to a directed colimit is witnessed at one stage. -/
@[stacks 07RG "finite-type algebra-map descent"]
theorem exists_finite
    {B C : Type x} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (φ : B →ₐ[A] C)
    (hfinite : (Algebra.TensorProduct.map φ (AlgHom.id A R∞)).Finite)
    (hφ : φ.FiniteType) :
    ∃ i : I, (Algebra.TensorProduct.map φ (AlgHom.id A (R i))).Finite := sorry

/-- Stacks tag `07RH`: surjectivity of the base change of a finite-type
algebra map to a directed colimit is witnessed at one stage. -/
@[stacks 07RH "finite-type algebra-map descent"]
theorem exists_surjective
    {B C : Type x} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (φ : B →ₐ[A] C)
    (hsurjective : Function.Surjective (Algebra.TensorProduct.map φ (AlgHom.id A R∞)))
    (hφ : φ.FiniteType) :
    ∃ i : I, Function.Surjective (Algebra.TensorProduct.map φ (AlgHom.id A (R i))) := sorry

end Ring.DirectLimit.Algebra.BaseChange.FiniteType
