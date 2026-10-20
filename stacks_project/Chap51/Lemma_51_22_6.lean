module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Cohomology.PowerSlice
import StacksCheckRecall

@[expose] public section

open scoped BigOperators

noncomputable section

universe u v

namespace AlgebraicGeometry.IsBlowup

/- Lemma 51.22.6. Let `q₀ = q(Gr_I(A))` and `d = d(Gr_I(A))`. For an
`(A, n, c)`-module `M`, the transition of every `A`-linear map
`M → I ^ n / I ^ (2 * n)` to the fixed-width slice beginning at
`n - (1 + d) * c` is a finite sum of maps from the slice beginning at
`n - (2 + d) * c`, multiplied by coefficients in `I ^ c`. -/
@[stacks 0GAC] #check (AlgebraicGeometry.IsBlowup.powerSliceTransition_eq_sum_smul :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (n c : ℕ) (hcn : c ≤ n) (M : ModuleCat.{v} (A ⧸ I ^ n))
    [Module.Finite (A ⧸ I ^ n) M]
    (hM : Module.IsIdealProjective
      (Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) M)
    (φ : (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).obj M →ₗ[A]
      Ideal.PowerSlice I A n n)
    (hn : max
      (associatedGradedUniformityThreshold I +
        (1 + associatedGradedFiberDimension I) * c)
      ((2 + associatedGradedFiberDimension I) * c) ≤ n)
    (hd : associatedGradedFiberDimension I = 0 →
      associatedGradedUniformityThreshold I + 2 * c ≤ n),
    ∃ k : ℕ, ∃ a : Fin k → (I ^ c : Ideal A),
      ∃ ψ : Fin k →
        (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).obj M →ₗ[A]
          Ideal.PowerSlice I A
            (n - (2 + associatedGradedFiberDimension I) * c) n,
        (Ideal.PowerSlice.transition I A n n
          (n - (1 + associatedGradedFiberDimension I) * c)
          (Nat.sub_le n ((1 + associatedGradedFiberDimension I) * c))).comp φ =
          ∑ i, (Ideal.PowerSlice.smulTo I A n
            (n - (2 + associatedGradedFiberDimension I) * c)
            (n - (1 + associatedGradedFiberDimension I) * c) c (a i)
            (Ideal.PowerSlice.coefficientIndex_le n c
              (associatedGradedFiberDimension I))).comp (ψ i))

end AlgebraicGeometry.IsBlowup
