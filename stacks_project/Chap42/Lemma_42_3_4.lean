module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.DifferentialRescale.Multiplicity
import StacksCheckRecall

/-!
# Multiplicity After Scaling One Differential
-/

@[expose] public section

open CategoryTheory

universe u v

/- Lemma 42.3.4 (1): scaling the degree-zero differential subtracts the multiplicity of
the zero/scalar complex on its image. -/
@[stacks 0EAC] #check
  (CategoryTheory.TwoPeriodicEndomorphism.multiplicity_smulD₀ :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) [Module.Finite R K.X]
      (x : R) (h₀ : IsFiniteLength R (K.toCochainComplex.homology 0))
      (h₁ : IsFiniteLength R (K.toCochainComplex.homology 1))
      (hMx : Module.supportDim R (QuotSMulTop x K.X) ≤ 0),
      (TwoPeriodicEndomorphism.smulD₀ K x).multiplicity
          (TwoPeriodicEndomorphism.smulD₀_homology_isFiniteLength K x h₀ h₁ hMx 0)
          (TwoPeriodicEndomorphism.smulD₀_homology_isFiniteLength K x h₀ h₁ hMx 1) =
        K.multiplicity h₀ h₁ -
          (TwoPeriodicEndomorphism.ofZeroScalar (LinearMap.range K.d₀.hom) x).multiplicity
            (TwoPeriodicEndomorphism.rangeOfZeroScalar_homology_isFiniteLength
              K.d₀.hom x hMx 0)
            (TwoPeriodicEndomorphism.rangeOfZeroScalar_homology_isFiniteLength
              K.d₀.hom x hMx 1))

/- Lemma 42.3.4 (2): scaling the degree-one differential adds the multiplicity of
the zero/scalar complex on its image. -/
@[stacks 0EAC] #check
  (CategoryTheory.TwoPeriodicEndomorphism.multiplicity_smulD₁ :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) [Module.Finite R K.X]
      (x : R) (h₀ : IsFiniteLength R (K.toCochainComplex.homology 0))
      (h₁ : IsFiniteLength R (K.toCochainComplex.homology 1))
      (hMx : Module.supportDim R (QuotSMulTop x K.X) ≤ 0),
      (TwoPeriodicEndomorphism.smulD₁ K x).multiplicity
          (TwoPeriodicEndomorphism.smulD₁_homology_isFiniteLength K x h₀ h₁ hMx 0)
          (TwoPeriodicEndomorphism.smulD₁_homology_isFiniteLength K x h₀ h₁ hMx 1) =
        K.multiplicity h₀ h₁ +
          (TwoPeriodicEndomorphism.ofZeroScalar (LinearMap.range K.d₁.hom) x).multiplicity
            (TwoPeriodicEndomorphism.rangeOfZeroScalar_homology_isFiniteLength
              K.d₁.hom x hMx 0)
            (TwoPeriodicEndomorphism.rangeOfZeroScalar_homology_isFiniteLength
              K.d₁.hom x hMx 1))
