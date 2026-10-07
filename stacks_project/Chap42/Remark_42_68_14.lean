module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Determinant
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {R : Type u} [CommRing R] [IsLocalRing R]

/- Remark 42.68.14: for nonzero determinant symbols of the two differential ranges,
the two short-exact concatenations differ by the signed determinant of the exact
finite-length two-periodic complex. -/
@[stacks 02PK] #check (CategoryTheory.TwoPeriodicEndomorphism.determinant_symbol :
  ∀ (K : TwoPeriodicEndomorphism (ModuleCat.{v} R))
    (hM : IsFiniteLength R K.X) (hK : K.toCochainComplex.Acyclic)
    (x : Module.FiniteLengthDeterminant.Symbol R (LinearMap.range K.d₀.hom)
      (range_d₀_isFiniteLength K hM))
    (hx : Module.FiniteLengthDeterminant.symbol R (LinearMap.range K.d₀.hom)
      (range_d₀_isFiniteLength K hM) x ≠ 0)
    (y : Module.FiniteLengthDeterminant.Symbol R (LinearMap.range K.d₁.hom)
      (range_d₁_isFiniteLength K hM))
    (hy : Module.FiniteLengthDeterminant.symbol R (LinearMap.range K.d₁.hom)
      (range_d₁_isFiniteLength K hM) y ≠ 0),
    Module.FiniteLengthDeterminant.exactEquiv (d₁RangeSequence K)
        (range_d₀_isFiniteLength K hM) hM (range_d₁_isFiniteLength K hM)
        (d₁RangeSequence_shortExact K hK)
        (Module.FiniteLengthDeterminant.symbol R (LinearMap.range K.d₀.hom)
            (range_d₀_isFiniteLength K hM) x ⊗ₜ[IsLocalRing.ResidueField R]
          Module.FiniteLengthDeterminant.symbol R (LinearMap.range K.d₁.hom)
            (range_d₁_isFiniteLength K hM) y) =
      (((-1) ^ ((Module.length R (LinearMap.range K.d₀.hom)).toNat *
            (Module.length R (LinearMap.range K.d₁.hom)).toNat) *
          determinant K hM hK : (IsLocalRing.ResidueField R)ˣ) :
        IsLocalRing.ResidueField R) •
        Module.FiniteLengthDeterminant.exactEquiv (d₀RangeSequence K)
          (range_d₁_isFiniteLength K hM) hM (range_d₀_isFiniteLength K hM)
          (d₀RangeSequence_shortExact K hK)
          (Module.FiniteLengthDeterminant.symbol R (LinearMap.range K.d₁.hom)
              (range_d₁_isFiniteLength K hM) y ⊗ₜ[IsLocalRing.ResidueField R]
            Module.FiniteLengthDeterminant.symbol R (LinearMap.range K.d₀.hom)
              (range_d₀_isFiniteLength K hM) x))

end CategoryTheory.TwoPeriodicEndomorphism
