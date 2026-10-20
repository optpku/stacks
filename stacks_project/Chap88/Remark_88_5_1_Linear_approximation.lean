module

public import ReasLib.RingTheory.AdicCompletion.Polynomial.LinearApproximation
import StacksCheckRecall

/-!
# Linear approximation of maps out of completed polynomial rings
-/

@[expose] public section

noncomputable section

universe u

open Algebra.NaiveCotangent.Adic

/- Remark 88.5.1 (Linear approximation): Let `I` be a finitely generated ideal of a
ring `A` and let `C` be an `I`-adically complete `A`-algebra. Given an `A`-algebra
map `ψ : polynomialCompletion A I ι →ₐ[A] C` (the algebraic packaging of a continuous
map out of `A[x_ι]^∧` into an `I`-adically complete algebra, cf. Formal Spaces,
Remark 87.28.1) and a tuple `δ : ι → C`, the shifted map `aevalShift ψ δ` sending
`X I i` to `ψ (X I i) + δ i` satisfies
`aevalShift ψ δ g = ψ g + ∑ i, ψ (pderiv I i g) * δ i + ξ`
with remainder `ξ ∈ (Ideal.span (Set.range δ)) ^ 2`. -/
@[stacks 0AK3] #check (Algebra.NaiveCotangent.Adic.linearApproximation :
  ∀ {A C ι : Type u} [CommRing A] [CommRing C] [Algebra A C]
    [Fintype ι] {I : Ideal A} (hI : I.FG)
    [IsAdicComplete (I.map (algebraMap A C)) C]
    (ψ : polynomialCompletion A I ι →ₐ[A] C) (δ : ι → C)
    (g : polynomialCompletion A I ι),
    aevalShift ψ δ g - ψ g - ∑ i, ψ (pderiv I i g) * δ i ∈
      (Ideal.span (Set.range δ)) ^ 2)

/- The first-order expansion of `aevalShift` as an equality in
`C ⧸ (Ideal.span (Set.range δ)) ^ 2`. -/
#check (Algebra.NaiveCotangent.Adic.linearApproximation_mk :
  ∀ {A C ι : Type u} [CommRing A] [CommRing C] [Algebra A C]
    [Fintype ι] {I : Ideal A} (hI : I.FG)
    [IsAdicComplete (I.map (algebraMap A C)) C]
    (ψ : polynomialCompletion A I ι →ₐ[A] C) (δ : ι → C)
    (g : polynomialCompletion A I ι),
    Ideal.Quotient.mk ((Ideal.span (Set.range δ)) ^ 2) (aevalShift ψ δ g) =
      Ideal.Quotient.mk _ (ψ g + ∑ i, ψ (pderiv I i g) * δ i))
