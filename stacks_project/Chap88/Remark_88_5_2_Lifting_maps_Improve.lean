/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Pi
public import stacks_project.Chap88.Remark_88_5_1_Linear_approximation_Aeval
public import stacks_project.Chap88.Remark_88_5_2_Lifting_maps_Obstruction

/-!
# Improved lifts of completed polynomial maps

This leaf owns the first-order shift `ψ'` of a lift `ψ` along a tuple `δ`, and
the descended algebra map `ψ'_{2n'} : B →ₐ[A] C ⧸ I^{2n'} C`.
-/

@[expose] public section

noncomputable section

universe u

open Algebra.NaiveCotangent.Adic

namespace Algebra.NaiveCotangent.Adic

variable {A B C ι : Type u} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C]

/-- The perturbation of `ψ` sending `X I i` to `ψ (X I i) - δ i`. -/
def improve {I : Ideal A} [IsAdicComplete (I.map (algebraMap A C)) C]
    (ψ : polynomialCompletion A I ι →ₐ[A] C) (δ : ι → C) :
    polynomialCompletion A I ι →ₐ[A] C :=
  aevalShift ψ fun i ↦ -δ i

/-- The improved map sends the indeterminate `X I i` to `ψ (X I i) - δ i`. -/
theorem improve_X {I : Ideal A} [IsAdicComplete (I.map (algebraMap A C)) C]
    (ψ : polynomialCompletion A I ι →ₐ[A] C) (δ : ι → C) (i : ι) :
    improve ψ δ (X I i) = ψ (X I i) - δ i :=
  sorry

/-- A `B`-linear homotopy `⊕ᵢ B dx_i → I^{n'} C / I^{2n'} C` along the reduction of `ψn`. -/
abbrev obstructionHomotopy (ι : Type u) {I : Ideal A} {n n' : ℕ} (hn : n' ≤ n)
    (ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n) : Type u :=
  @LinearMap B B _ _ (RingHom.id B) (ι → B) (adicPowQuotient I C n') _ _ _
    (moduleOfAlgHom I ((Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hn)).comp ψn))

/-- Unfolding of `obstructionHomotopy` as a `LinearMap` with the reduced `B`-action. -/
theorem obstructionHomotopy_eq (ι : Type u) {I : Ideal A} {n n' : ℕ} (hn : n' ≤ n)
    (ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n) :
    obstructionHomotopy ι hn ψn =
      @LinearMap B B _ _ (RingHom.id B) (ι → B) (adicPowQuotient I C n') _ _ _
        (moduleOfAlgHom I ((Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hn)).comp ψn)) :=
  sorry

/-- Precomposition of a homotopy with the Jacobian, as maps into `I^{n'} C / I^{2n'} C`. -/
def jacobianHomotopy [Fintype ι] {I : Ideal A} (P : Presentation A B I ι) {n n' : ℕ}
    (hn : n' ≤ n) (ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n)
    (h : obstructionHomotopy ι hn ψn) :
    @LinearMap B B _ _ (RingHom.id B) P.toExtension.Cotangent (adicPowQuotient I C n') _ _ _
      (moduleOfAlgHom I ((Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hn)).comp ψn)) :=
  @jacobianHom _ _ _ _ _ _ _ _ P (adicPowQuotient I C n') _
    (moduleOfAlgHom I ((Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hn)).comp ψn)) h

/-- Evaluating `jacobianHomotopy` is precomposition with `jacobian P`. -/
theorem jacobianHomotopy_apply [Fintype ι] {I : Ideal A} (P : Presentation A B I ι)
    {n n' : ℕ} (hn : n' ≤ n) (ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n)
    (h : obstructionHomotopy ι hn ψn) (x : P.toExtension.Cotangent) :
    jacobianHomotopy P hn ψn h x = h (jacobian P x) :=
  sorry

/-- On the presentation kernel, the improved map lands in `I^{2n'} C` when `δ i`
represents `h (dx_i)` for a homotopy of the coefficient-changed obstruction map
with `h ∘ jacobian`. -/
theorem improve_mem_pow [Fintype ι] [DecidableEq ι] {I : Ideal A} (hI : I.FG)
    [IsAdicComplete (I.map (algebraMap A C)) C] {P : Presentation A B I ι}
    {n n' : ℕ} (hn : n' ≤ n) {ψn : B →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n}
    (ψ : polynomialCompletion A I ι →ₐ[A] C) (hψ : IsLift P ψn ψ) (δ : ι → C)
    (hδ : ∀ i, δ i ∈ (I.map (algebraMap A C)) ^ n') (h : obstructionHomotopy ι hn ψn)
    (hcomm : map_obstructionHom hn hψ = jacobianHomotopy P hn ψn h)
    (hδh : ∀ i, toAdicPowQuotient I C n' ⟨δ i, hδ i⟩ = h (Pi.single i 1))
    {g : polynomialCompletion A I ι} (hg : g ∈ P.ker) :
    improve ψ δ g ∈ (I.map (algebraMap A C)) ^ (2 * n') :=
  sorry

/-- The kernel of the presentation map is contained in the kernel of
`mk^{2n'} ∘ improve` when `δ` comes from a homotopy of the coefficient-changed
obstruction map. -/
theorem improve_ker_le [Fintype ι] [DecidableEq ι] {I : Ideal A} (hI : I.FG)
    [IsAdicComplete (I.map (algebraMap A C)) C] {P : Presentation A B I ι}
    {n n' : ℕ} (hn : n' ≤ n) {ψn : B →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n}
    (ψ : polynomialCompletion A I ι →ₐ[A] C) (hψ : IsLift P ψn ψ) (δ : ι → C)
    (hδ : ∀ i, δ i ∈ (I.map (algebraMap A C)) ^ n') (h : obstructionHomotopy ι hn ψn)
    (hcomm : map_obstructionHom hn hψ = jacobianHomotopy P hn ψn h)
    (hδh : ∀ i, toAdicPowQuotient I C n' ⟨δ i, hδ i⟩ = h (Pi.single i 1)) :
    RingHom.ker P.toAlgHom.toRingHom ≤
      RingHom.ker
        ((Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^ (2 * n'))).comp
          (improve ψ δ)).toRingHom :=
  sorry

/-- The descended algebra map `ψ'_{2n'} : B →ₐ[A] C ⧸ I^{2n'} C` induced by
`improve`. -/
def improveAlgHom {I : Ideal A} [IsAdicComplete (I.map (algebraMap A C)) C]
    (P : Presentation A B I ι) {n' : ℕ} (ψ : polynomialCompletion A I ι →ₐ[A] C)
    (δ : ι → C)
    (hker : RingHom.ker P.toAlgHom.toRingHom ≤
      RingHom.ker
        ((Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^ (2 * n'))).comp
          (improve ψ δ)).toRingHom) :
    B →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ (2 * n') :=
  AlgHom.liftOfSurjective P.toAlgHom P.surjective
    ((Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^ (2 * n'))).comp (improve ψ δ)) hker

/-- Descent recovers `mk^{2n'} ∘ improve` on `A[x_ι]^∧`. -/
theorem improveAlgHom_comp {I : Ideal A}
    [IsAdicComplete (I.map (algebraMap A C)) C] (P : Presentation A B I ι) {n' : ℕ}
    (ψ : polynomialCompletion A I ι →ₐ[A] C) (δ : ι → C)
    (hker : RingHom.ker P.toAlgHom.toRingHom ≤
      RingHom.ker
        ((Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^ (2 * n'))).comp
          (improve ψ δ)).toRingHom) :
    (improveAlgHom P ψ δ hker).comp P.toAlgHom =
      (Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^ (2 * n'))).comp (improve ψ δ) :=
  sorry

/-- After factoring to `C ⧸ I^{n'} C`, the improved map agrees with `ψn` whenever
each `δ i` lies in `I^{n'} C`. -/
theorem improveAlgHom_comp_factor {I : Ideal A}
    [IsAdicComplete (I.map (algebraMap A C)) C] (P : Presentation A B I ι)
    {n n' : ℕ} (hn : n' ≤ n) (ψn : B →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n)
    (ψ : polynomialCompletion A I ι →ₐ[A] C) (hψ : IsLift P ψn ψ) (δ : ι → C)
    (hδ : ∀ i, δ i ∈ (I.map (algebraMap A C)) ^ n')
    (hker : RingHom.ker P.toAlgHom.toRingHom ≤
      RingHom.ker
        ((Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^ (2 * n'))).comp
          (improve ψ δ)).toRingHom) :
    (Ideal.Quotient.factorₐ A
          (Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left n' zero_lt_two))).comp
        (improveAlgHom P ψ δ hker) =
      (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hn)).comp ψn :=
  sorry

end Algebra.NaiveCotangent.Adic
