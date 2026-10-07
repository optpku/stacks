module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Finite
public import ReasLib.RingTheory.DirectLimit.Algebra.Base
public import ReasLib.RingTheory.EssentialFiniteness.Basic
public import ReasLib.RingTheory.Flat.Locus
import Mathlib.Tactic.CrossRefAttribute

/-!
# Descending a flat-locus condition along a directed colimit

This file owns the finite-stage descent of the closed-subset flatness condition for a finitely
presented algebra and module.

@stack 05LM
@stack 05LT
-/

@[expose] public section

noncomputable section

open PrimeSpectrum
open scoped TensorProduct

universe u v w x y

namespace Ring.DirectLimit.FlatLocus

variable {R : Type u} {S : Type v} {M : Type w} {Λ : Type x}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M]
variable [Algebra.FinitePresentation R S] [Module.FinitePresentation S M]
variable [Preorder Λ] [IsDirectedOrder Λ] [Nonempty Λ]

-- Local instance justification (instance diamond): make the direct-limit stage the right scalar
-- ring of each tensor product appearing in the source statement.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (A : Λ → Type y) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable (φ : ∀ i j, i ≤ j → A i →ₐ[R] A j)
variable [DirectedSystem A fun i j h ↦ (φ i j h : A i →+* A j)]
variable (I : ∀ i, Ideal (A i))

local notation "ρ" => fun i j h ↦ (φ i j h : A i →+* A j)
local notation "A∞" => Ring.DirectLimit A ρ
local notation "ι∞" => Ring.DirectLimit.of A ρ
local notation "I∞" => ⨆ i, Ideal.map (ι∞ i) (I i)
local notation "S∞" => S ⊗[R] A∞
local notation "M∞" => S∞ ⊗[S] M
local notation "S[" i "]" => S ⊗[R] A i
local notation "M[" i "]" => S[i] ⊗[S] M

/-- Lemma 15.18.3: if the closed-subset flatness condition holds after base change to a directed
colimit, then it already holds after base change to one stage. -/
@[stacks 05LM "Lemma 15.18.3"]
theorem exists_stage
    (hI : ∀ ⦃i j⦄, (hij : i ≤ j) → Ideal.map (ρ i j hij) (I i) ≤ I j)
    (hflat_inf :
      zeroLocus (Ideal.map (Algebra.algebraMap A∞ S∞) I∞ : Set S∞) ⊆
        Module.flatOverBaseLocus A∞ S∞ M∞) :
    ∃ i : Λ,
      zeroLocus (Ideal.map (Algebra.algebraMap (A i) S[i]) (I i) : Set S[i]) ⊆
        Module.flatOverBaseLocus (A i) S[i] M[i] := sorry

omit [Algebra.FinitePresentation R S] in
/-- Lemma 15.19.4: for an essentially finitely presented algebra, a closed-subset flatness
condition also involving a fixed ideal of the algebra descends from a directed colimit to one
stage. -/
@[stacks 05LT "Lemma 15.19.4"]
theorem exists_stage_add (J : Ideal S)
    (hS : RingHom.EssFinitePresentation (Algebra.algebraMap R S))
    (hI : ∀ ⦃i j⦄, (hij : i ≤ j) → Ideal.map (ρ i j hij) (I i) ≤ I j)
    (hflat_inf :
      zeroLocus
          ((Ideal.map (Algebra.algebraMap A∞ S∞) I∞ +
            Ideal.map (Algebra.algebraMap S S∞) J : Ideal S∞) : Set S∞) ⊆
        Module.flatOverBaseLocus A∞ S∞ M∞) :
    ∃ i : Λ,
      zeroLocus
          ((Ideal.map (Algebra.algebraMap (A i) S[i]) (I i) +
            Ideal.map (Algebra.algebraMap S S[i]) J : Ideal S[i]) : Set S[i]) ⊆
        Module.flatOverBaseLocus (A i) S[i] M[i] := sorry

end Ring.DirectLimit.FlatLocus
