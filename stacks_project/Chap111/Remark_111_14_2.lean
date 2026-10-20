module

public import ReasLib.RingTheory.LocalRing.OrdinaryDoublePoint
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

open MvPowerSeries QuadraticMap

/- Remark 111.14.2 (1): a singularity on a curve over a field `k` is called an ordinary double
point when its complete local ring has the finite-separable power-series quotient presentation
captured by `IsOrdinaryDoublePointRing`. -/
@[stacks 02DN] #check
  (IsOrdinaryDoublePointRing :
    ∀ (k A : Type u) [Field k] [CommRing A] [Algebra k A], Prop)

/- Remark 111.14.2 (2): isomorphism classes of these rings are indexed by equivalent pairs. -/
@[stacks 02DN] #check
  (ordinaryDoublePointRing_iso_iff_quadraticPair :
    ∀ (k k₁ k₂ : Type u) [Field k] [Field k₁] [Field k₂] [Algebra k k₁] [Algebra k k₂]
      [FiniteDimensional k k₁] [Algebra.IsSeparable k k₁]
      [FiniteDimensional k k₂] [Algebra.IsSeparable k k₂]
      (f₁ : MvPowerSeries (Fin 2) k₁) (a₁ b₁ c₁ : k₁)
      (hf₁ : hasNondegenerateQuadraticInitial f₁ a₁ b₁ c₁)
      (f₂ : MvPowerSeries (Fin 2) k₂) (a₂ b₂ c₂ : k₂)
      (hf₂ : hasNondegenerateQuadraticInitial f₂ a₂ b₂ c₂),
      Nonempty
          ((MvPowerSeries (Fin 2) k₁ ⧸ Ideal.span {f₁}) ≃ₐ[k]
            (MvPowerSeries (Fin 2) k₂ ⧸ Ideal.span {f₂})) ↔
        binaryQuadratic.EquivalentPair k k₁ k₂ a₁ b₁ c₁ a₂ b₂ c₂)
