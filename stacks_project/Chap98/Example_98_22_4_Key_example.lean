/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Deformation.PresentedAlgebra

/-!
# Example 98.22.4 (Key example)

The naive-cotangent obstruction theory for a finite polynomial quotient over a
Noetherian ring, with its presentation, module comparisons, evaluation formula,
lifting criterion, naturality, and derived-composition description.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry Algebra Algebra.Generators Algebra.Extension
open MvPolynomial
open scoped NaiveCotangent
noncomputable section
universe u

variable {Λ ι : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Finite ι]
variable (J : Ideal (MvPolynomial ι Λ))

/- Example 98.22.4 (Key example): the affine slice carries the cotangent
obstruction theory. -/
@[stacks 07YI] #check (AlgebraicGeometry.Deformation.PresentedAlgebra.theory J :
  AlgebraicGeometry.GroupoidsOver.ObstructionTheory
    (AlgebraicGeometry.Deformation.PresentedAlgebra.presentedSlice J))

#check (Algebra.Extension.NaiveCotangent.generatorsHomotopyEquiv
    (Generators.self Λ (MvPolynomial ι Λ ⧸ J)) (Generators.naive (I := J)) :
  HomotopyEquiv (NL{(MvPolynomial ι Λ ⧸ J) ⁄ Λ})
    (Extension.NaiveCotangent.complex (Generators.naive (I := J)).toExtension))

#check (Algebra.Generators.naive_val _ (Function.surjInv_eq Ideal.Quotient.mk_surjective) :
  ∀ i : ι, (Generators.naive (I := J)).val i = Ideal.Quotient.mk J (MvPolynomial.X i))

#check (Algebra.Generators.ker_naive _ _ : (Generators.naive (I := J)).ker = J)

#check (Algebra.Generators.cotangentSpaceBasis (Generators.naive (I := J)) :
  Module.Basis ι (MvPolynomial ι Λ ⧸ J)
    (Generators.naive (I := J)).toExtension.CotangentSpace)

variable {A' A : Type u} [CommRing A'] [CommRing A]
variable [Algebra Λ A'] [Algebra Λ A]
variable (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
variable (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)

namespace Algebra.NaiveCotangent.Obstruction

#check (Algebra.NaiveCotangent.Obstruction.module_spec π J φ :
  Function.Bijective (homCokerMap π J φ) ∧
      Function.Bijective (extMap π J φ) ∧
      Function.Bijective (baseChangeExtMap π J φ))

#check (Algebra.NaiveCotangent.Obstruction.relationMap_apply π J φ :
  ∀ (a' : ι → A') (ha' : ∀ i, π (a' i) = φ ((Generators.naive (I := J)).val i))
    (f : (Generators.naive (I := J)).ker),
    (relationMap π J φ a' ha' (Cotangent.mk f)).1 = aeval a' f.1)

#check (Algebra.NaiveCotangent.Obstruction.obstruction_eq_ofLifts π J φ :
  ∀ (a' : ι → A') (ha' : ∀ i, π (a' i) = φ ((Generators.naive (I := J)).val i)),
    obstruction π J φ = ofLifts π J φ a' ha')

#check (Algebra.NaiveCotangent.Obstruction.independent π J φ :
  ∀ (a₁ a₂ : ι → A')
    (ha₁ : ∀ i, π (a₁ i) = φ ((Generators.naive (I := J)).val i))
    (ha₂ : ∀ i, π (a₂ i) = φ ((Generators.naive (I := J)).val i)),
    ofLifts π J φ a₁ ha₁ = ofLifts π J φ a₂ ha₂)

#check (Algebra.NaiveCotangent.Obstruction.eq_zero_iff_hasLift π J φ :
  obstruction π J φ = 0 ↔ AlgHom.HasLift π φ)

#check (Algebra.NaiveCotangent.Obstruction.eq_composition π J φ :
  baseChangeExtMap π J φ (obstruction π J φ) = composition π J φ)

variable {B' B : Type u} [CommRing B'] [CommRing B]
variable [Algebra Λ B'] [Algebra Λ B]
variable (ρ : B' →ₐ[Λ] B) [ρ.toRingHom.IsSquareZeroExtension]
variable (ψ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] B)
variable (τ : A' →ₐ[Λ] B') (σ : A →ₐ[Λ] B)
variable (hcomm : ρ.comp τ = σ.comp π) (hφψ : ψ = σ.comp φ)

#check (Algebra.NaiveCotangent.Obstruction.map_obstruction π ρ J φ ψ τ σ hcomm hφψ :
  map π ρ J φ ψ τ σ hcomm hφψ (obstruction π J φ) = obstruction ρ J ψ)

end Algebra.NaiveCotangent.Obstruction
