/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Remark_88_5_1_Linear_approximation_Aeval

/-!
# Linear approximation of maps out of completed polynomial rings
-/

@[expose] public section

noncomputable section

universe u

open Algebra.NaiveCotangent.Adic

namespace Algebra.NaiveCotangent.Adic

variable {A C ι : Type u} [CommRing A] [CommRing C] [Algebra A C]

/-- Remark 88.5.1 (Linear approximation): Let `I` be a finitely generated ideal of a
ring `A` and let `C` be an `I`-adically complete `A`-algebra. Given an `A`-algebra
map `ψ : polynomialCompletion A I ι →ₐ[A] C` (the algebraic packaging of a continuous
map out of `A[x_ι]^∧` into an `I`-adically complete algebra, cf. Formal Spaces,
Remark 87.28.1) and a tuple `δ : ι → C`, the shifted map `aevalShift ψ δ` sending
`X I i` to `ψ (X I i) + δ i` satisfies
`aevalShift ψ δ g = ψ g + ∑ i, ψ (pderiv I i g) * δ i + ξ`
with remainder `ξ ∈ (Ideal.span (Set.range δ)) ^ 2`. -/
@[stacks 0AK3]
theorem linearApproximation [Fintype ι] {I : Ideal A} (hI : I.FG)
    [IsAdicComplete (I.map (algebraMap A C)) C]
    (ψ : polynomialCompletion A I ι →ₐ[A] C) (δ : ι → C)
    (g : polynomialCompletion A I ι) :
    aevalShift ψ δ g - ψ g - ∑ i, ψ (pderiv I i g) * δ i ∈
      (Ideal.span (Set.range δ)) ^ 2 :=
  sorry

/-- The first-order expansion of `aevalShift` as an equality in
`C ⧸ (Ideal.span (Set.range δ)) ^ 2`. -/
theorem linearApproximation_mk [Fintype ι] {I : Ideal A} (hI : I.FG)
    [IsAdicComplete (I.map (algebraMap A C)) C]
    (ψ : polynomialCompletion A I ι →ₐ[A] C) (δ : ι → C)
    (g : polynomialCompletion A I ι) :
    Ideal.Quotient.mk ((Ideal.span (Set.range δ)) ^ 2) (aevalShift ψ δ g) =
      Ideal.Quotient.mk _ (ψ g + ∑ i, ψ (pderiv I i g) * δ i) :=
  sorry

end Algebra.NaiveCotangent.Adic
